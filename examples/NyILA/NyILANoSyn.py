import ila
SCALAR_REG_BITS = 32
SCALAR_REGS_PER_MACHINE = 32
PC_BITS = 32
VECTOR_LANE_BITS = 32
VECTOR_LANES_PER_REG = 16
VECTOR_REGS_PER_MACHINE = 32
VECTOR_MASK_REG_BITS = 32
MEM_ADDRESS_BITS = 32

class NyEncoding:
	OR  = 0b000000
	AND = 0b000001
	XOR = 0b000011
	ADD_I = 0b000101
	SUB_I = 0b000110
	MULL_I = 0b000111 #low 32 bits mult
	MULH_U = 0b001000 #high 32 bits mult
	ASHR = 0b001001
	SHR = 0b001010
	SHL = 0b001011
	CLZ = 0b001100
	SHUFFLE = 0b001101
	CTZ = 0b001110
	MOVE = 0b001111
	CMPEQ_I = 0b010000
	CMPNE_I = 0b010001
	CMPGT_I = 0b010010
	CMPLT_I = 0b010100
	CMPLE_I = 0b010101
	CMPGT_U = 0b010110
	CMPGE_U = 0b010111
	CMPLT_U = 0b011000
	CMPLE_U = 0b011001
	GETLANE = 0b011010
	FTOI = 0b011011
	RECIPROCAL = 0b011100
	SEXT8 = 0b011101
	SEXT16 = 0b011110
	MULH_I = 0b011111

	ADD_F = 0b100000
	SUB_F = 0b100001
	Mul_F = 0b100010
	ITOF = 0b101010
	CMPGT_F = 0b101100
	CMPGE_F = 0b101101
	CMPLT_F = 0b101110
	CMPLE_F = 0b101111
	CMPEQ_F = 0b110000
	CMPNE_F = 0b110001
	BREAK = 0b111110
	SYSCALL = 0b111111

	B0 = 0b000
	BZ = 0b001
	BNZ = 0b010
	B1 = 0b011
	CALL0 = 0b100
	CALL1 = 0b110
	ERET = 0b111

class nyGPUModel:
	def __init__(self):
		self.model = ila.Abstraction('nyGPU')
		self.createStates()

	def createStates(self):
		self.createPC()
		self.createRegs()
		self.mem = self.model.mem('mem', MEM_ADDRESS_BITS, MEM_ADDRESS_BITS)		
		self.instructionFetch()
		self.addInstruction()

	def createPC(self):
		self.pc = self.model.reg('pc', PC_BITS)

	def createRegs(self):
		self.scalar_registers = []
		for scalar_index in xrange(SCALAR_REGS_PER_MACHINE):
			self.scalar_registers.append(self.model.reg('SREG_' + str(scalar_index), SCALAR_REG_BITS))
		self.vector_registers = []
		for vector_index in xrange(VECTOR_REGS_PER_MACHINE):
			self.vector_registers.append([])
			for vector_lane in xrange(VECTOR_LANES_PER_REG):
				self.vector_registers[vector_index].append(self.model.reg('VREG_' + str(vector_index) + '_' + str(vector_lane), VECTOR_LANE_BITS))
		self.vector_mask_register = self.model.reg('vector_mask_register', VECTOR_MASK_REG_BITS)

	def indexToSGPR(self, regNo):	
		SGPR = self.scalar_registers[0]
		for idx in xrange(SCALAR_REGS_PER_MACHINE):
			SGPR = ila.ite(regNo == idx, self.scalar_registers[idx], SGPR)
		return SGPR

	def indexToVGPR(self, regNo, laneNo):
		VGPR = self.vector_registers[0][0]
		for regIdx in xrange(VECTOR_REGS_PER_MACHINE):
 			for laneIdx in xrange(VECTOR_LANES_PER_REG):
				VGPR = ila.ite((regNo == regIdx) & (laneNo == laneIdx), self.vector_registers[regIdx][laneIdx], VGPR)
		return VGPR

	def instructionFetch(self):
		self.instruction = ila.load(self.mem, ila.zero_extend(self.pc[31:2], MEM_ADDRESS_BITS))
		self.isBranch = (self.instruction[31:28] == self.model.const(0b1111, 4))
		self.branchOP = self.instruction[27:25]
		self.branchOffsetA = self.instruction[24:5]
		self.branchSrc = self.instruction[4:0]
		self.branchOffsetB = self.instruction[24:0]
		self.isRegReg = (self.instruction[31:29] == self.model.const(0b110,3))
		self.rrType = self.instruction[28:26]
		self.rrOpcode = self.instruction[25:20]
		self.rrSrc2 = self.instruction[19:15]
		self.rrMask = self.instruction[14:10]
		self.rrDest = self.instruction[9:5]
		self.rrSrc1 = self.instruction[4:0]
		self.isImmediate = (self.instruction[31] == self.model.const(0b0, 1))
		self.immType = self.instruction[30:29]
		self.immOpcode = self.instruction[28:24]
		self.immA = ila.zero_extend(self.instruction[23:15], SCALAR_REG_BITS)
		self.immB = ila.zero_extend(self.instruction[23:10], SCALAR_REG_BITS)
		self.immCup = self.instruction[23:10]
		self.immClow = self.instruction[4:0]
		self.immDest = self.instruction[9:5]
		self.immMask = self.instruction[14:10]
		self.imm = ila.ite(self.immType[1] == self.model.const(0b0, 1), ila.zero_extend(self.immB, SCALAR_REG_BITS), ila.ite(self.immType == self.model.const(0b10, 2), ila.zero_extend(ila.concat(self.immCup, self.immClow), SCALAR_REG_BITS), ila.ite(self.immType == self.model.const(0b11, 2), ila.zero_extend(self.immA, SCALAR_REG_BITS), ila.zero_extend(self.immA, SCALAR_REG_BITS))))
		self.isMem = (self.instruction[31:30] == self.model.const(0b10, 2))
		self.isLoad = self.instruction[29]
		self.memOpcode = self.instruction[28:25]
		self.memOffSetA = self.instruction[24:15]
		self.memOffSetB = self.instruction[24:10]
		self.memMask = self.instruction[14:10]
		self.memDest = self.instruction[9:5]
		self.memSrc = self.instruction[9:5]
		self.memPtr = self.instruction[4:0]
		self.memOffSet = ila.ite(self.memOpcode == self.model.const(0b1000, 4), ila.sign_extend(self.memOffSetA, SCALAR_REG_BITS), ila.ite(self.memOpcode == self.model.const(0b1110, 4), ila.sign_extend(self.memOffSetA, SCALAR_REG_BITS), ila.sign_extend(self.memOffSetB, SCALAR_REG_BITS)))
		self.isMask = (((self.rrType == self.model.const(0b010, 3)) | (self.rrType == self.model.const(0b101, 3))) & self.isRegReg) #need rewrite
 		self.dest = self.instruction[9:5]

	def pc_nxt(self):
		sreg1 = self.indexToSGPR(self.branchSrc)
		pcPlus4 = self.pc + self.model.const(0b100, PC_BITS)
		return pcPlus4
		#return ila.choice('pc_nxt', [pcPlus4, sreg1, ila.ite(sreg1 == 0, ila.zero_extend(self.branchOffsetA, PC_BITS), pcPlus4), \
		#	ila.ite(sreg1 != 0, ila.zero_extend(self.branchOffsetA, PC_BITS), pcPlus4), ila.zero_extend(self.branchOffsetA, PC_BITS)])	#call and return need to set other registers

	def sreg_nxt(self, regNo):
		sreg1 = self.indexToSGPR(self.rrSrc1)
		sreg2 = self.indexToSGPR(self.rrSrc2)
    	#load instruction
		addr = self.indexToSGPR(self.memPtr) + ila.sign_extend(self.memOffSet, SCALAR_REG_BITS)
		load_val = ila.load(self.mem, ila.zero_extend(addr[31:2], MEM_ADDRESS_BITS))

		return ila.ite(self.dest == regNo,\
					ila.ite(self.isRegReg, 
						ila.ite(self.rrType == self.model.const(0b000, 3), 
							ila.ite(self.rrOpcode == NyEncoding.ADD_I, sreg1 + sreg2, 
							ila.ite(self.rrOpcode == NyEncoding.SUB_I, sreg1 - sreg2, 
							ila.ite(self.rrOpcode == NyEncoding.AND, sreg1 & sreg2,
							ila.ite(self.rrOpcode == NyEncoding.OR, sreg1 | sreg2, 
							ila.ite(self.rrOpcode == NyEncoding.MULH_I, self.auxMull_i(sreg1, sreg2), 
							ila.ite(self.rrOpcode == NyEncoding.MULH_U, self.auxMulh_u(sreg1, sreg2), 
							ila.ite(self.rrOpcode == NyEncoding.ASHR, ila.ashr(sreg1, sreg2[4:0]), 
							ila.ite(self.rrOpcode == NyEncoding.SHR, sreg1 >> sreg2[4:0],
							ila.ite(self.rrOpcode == NyEncoding.SHL, sreg1 << sreg2[4:0],
							ila.ite(self.rrOpcode == NyEncoding.CLZ, self.aux_clz(sreg2),
							ila.ite(self.rrOpcode == NyEncoding.CTZ, self.aux_ctz(sreg2),
							ila.ite(self.rrOpcode == NyEncoding.MOVE, sreg2,
							ila.ite(self.rrOpcode == NyEncoding.CMPEQ_I, ila.ite(sreg1 == sreg2, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPNE_I, ila.ite(sreg1 != sreg2, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPGT_I, ila.ite(self.auxCmpgt_i(sreg1, sreg2) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPGE_I, ila.ite(self.auxCmpge_i(sreg1, sreg2) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPLT_I, ila.ite(self.auxCmplt_i(sreg1, sreg2) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPLE_I, ila.ite(self.auxCmple_i(sreg1, sreg2) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPGT_U, ila.ite(sreg1 > sreg2, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPGE_U, ila.ite(sreg1 < sreg2, self.const(0b0, SCALAR_REG_BITS), self.const(0xffff, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPLT_U, ila.ite(sreg1 < sreg2, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(self.rrOpcode == NyEncoding.CMPLE_U, ila.ite(sreg1 > sreg2, self.const(0b0, SCALAR_REG_BITS), self.const(0xffff,SCALAR_REG_BITS)),
								self.scalar_registers[regNo]))))))))))))))))))))))
							, self.scalar_registers[regNo]),\
					ila.ite(self.isImmediate, 
						ila.ite(self.immType == self.model.const(0b00, 2), 
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.ADD_I, sreg1 + self.immB, 
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.SUB_I, sreg1 - self.immB,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.AND, sreg1 & self.immB,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.OR, sreg1 | self.immB,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.MULH_I, self.auxMull_i(sreg1, self.immB),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.MULL_I, self.auxMulh_u(sreg1, self.immB),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.ASHR, ila.ashr(sreg1, self.immB[4:0]),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.SHR, sreg1 >> self.immB[4:0],
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.SHL, sreg1 << self.immB[4:0],
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CLZ, sreg1, self.aux_clz(self.immB),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CTZ, sreg1, self.aux_ctz(self.immB),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.MOVE, self.immB,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPEQ_I, ila.ite(sreg1 == self.immB, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPNE_I, ila.ite(sreg1 != self.immB, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPGT_I, ila.ite(self.auxCmpgt_i(sreg1, self.immB) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPGE_I, ila.ite(self.auxCmpge_i(sreg1, self.immB) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPLT_I, ila.ite(self.auxCmplt_i(sreg1, self.immB) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPLE_I, ila.ite(self.auxCmple_i(sreg1, self.immB) == self.getConstOne(), self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPGT_U, ila.ite(sreg1 > self.immB, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPGE_U, ila.ite(sreg1 < self.immB, self.const(0b0, SCALAR_REG_BITS), self.const(0xffff, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPLT_U, ila.ite(sreg1 < self.immB, self.const(0xffff, SCALAR_REG_BITS), self.const(0b0, SCALAR_REG_BITS)),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.CMPLE_U, ila.ite(sreg1 > self.immB, self.const(0b0, SCALAR_REG_BITS), self.const(0xffff,SCALAR_REG_BITS)),
							 self.scalar_registers[regNo])))))))))))))))))))))),\
						ila.ite(self.immType == self.model.const(0b10, 2),
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.ADD_I, sreg1 + self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.SUB_I, sreg1 - self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.AND, sreg1 & self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.OR, sreg1 | self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.MULH_I, sreg1 * sreg2, self.scalar_registers[regNo]))))),\
							self.scalar_registers[regNo])),\
					ila.ite(self.isLoad == self.model.const(0b1, 1), self.scalar_registers[regNo], self.scalar_registers[regNo]))),\
				self.scalar_registers[regNo])

		# return ila.choice('reg_' + str(regNo) + '_nxt',\
  #   		[self.scalar_registers[regNo], ila.ite( regNo == self.rrDest,
  #   	ila.choice('reg_' + str(regNo) + '_nxt',\
  #   	 [dest,\
  #   	  sreg1 | sreg2,\
  #   	  sreg1 & sreg2,\
  #   	  sreg1 ^ sreg2,\
  #   	  sreg1 + sreg2,\
  #   	  sreg1 - sreg2,\
  #   	  sreg1 * sreg2
    	  # (ila.zero_extend(sreg1, 64) * ila.zero_extend(sreg2, 64))[63:31],\
    	  # ila.ashr(sreg1, sreg2[4:0]),\
    	  # sreg1 >> sreg2[4:0],\
    	  # sreg1 << sreg2[4:0],\
    	  # self.aux_clz(sreg2),\
    	  # self.aux_ctz(sreg2),\
    	  # ila.ite(laneNo == -1, dest, self.indexToVGPR(self.rrSrc1, sreg2)),\
    	  # sreg2,\
    	  # (sreg1 == sreg2),\
    	  # (sreg1 != sreg2),\
    	  # (sreg1 > sreg2),\
    	  # (sreg1 >= sreg2),\
    	  # (sreg1 < sreg2),\
    	  # (sreg1 <= sreg2),\
    	  # sreg1 | self.imm,\
    	  # sreg1 & self.imm,\
    	  # sreg1 ^ self.imm,\
    	  # sreg1 + self.imm,\
    	  # sreg1 - self.imm,\
    	  # sreg1 * self.imm,\
    	  # (ila.zero_extend(sreg1, 64) * ila.zero_extend(self.imm, 64))[63:31],\
    	  # ila.ashr(sreg1, self.imm[4:0]),\
    	  # sreg1 >> self.imm[4:0],\
    	  # sreg1 << self.imm[4:0],\
    	  # self.aux_clz(self.imm),\
    	  # self.aux_ctz(self.imm),\
    	  # ila.ite(laneNo == -1, dest, self.indexToVGPR(self.rrSrc1, self.imm)),\
    	  # self.imm,\
    	  # ila.zero_extend(load_val[7:0], SCALAR_REG_BITS),\
    	  # ila.zero_extend(load_val[15:0], SCALAR_REG_BITS),\
    	  # ila.sign_extend(load_val[7:0], SCALAR_REG_BITS),\
    	  # ila.sign_extend(load_val[15:0], SCALAR_REG_BITS),\
    	  # load_val
    	  #]), self.scalar_registers[regNo])])

	def vreg_nxt(self, regNo, laneNo):
		ssreg1 = self.indexToSGPR(self.rrSrc1)
		ssreg2 = self.indexToSGPR(self.rrSrc2)
		vsreg1 = self.indexToVGPR(self.rrSrc1, self.model.const(laneNo, SCALAR_REG_BITS))
		vsreg2 = self.indexToVGPR(self.rrSrc2, self.model.const(laneNo, SCALAR_REG_BITS))
		mask = self.indexToSGPR(self.rrMask)

    	#load instruction
		addr = self.indexToSGPR(self.memPtr) + ila.sign_extend(self.memOffSet, SCALAR_REG_BITS)
		load_val = ila.load(self.mem, ila.zero_extend(addr[31:2], PC_BITS))

		return ila.ite(self.dest == regNo, 
				ila.ite(self.isRegReg,
					ila.ite(self.rrType == self.model.const(0b001, 3), 
						ila.ite(self.rrOpcode == NyEncoding.ADD_I, vsreg1 + ssreg2,
						ila.ite(self.rrOpcode == NyEncoding.SUB_I, vsreg1 - ssreg2,
						ila.ite(self.rrOpcode == NyEncoding.AND, vsreg1 & ssreg2, 
						ila.ite(self.rrOpcode == NyEncoding.OR, vsreg1 | ssreg2, 
						ila.ite(self.rrOpcode == NyEncoding.MULH_I, vsreg1 * ssreg2, self.vector_registers[regNo][laneNo]))))),
					ila.ite(self.rrType == self.model.const(0b100, 3),
						ila.ite(self.rrOpcode == NyEncoding.ADD_I, vsreg1 + vsreg2,
						ila.ite(self.rrOpcode == NyEncoding.SUB_I, vsreg1 - vsreg2,
						ila.ite(self.rrOpcode == NyEncoding.AND, vsreg1 & vsreg2, 
						ila.ite(self.rrOpcode == NyEncoding.OR, vsreg1 | vsreg2, 
						ila.ite(self.rrOpcode == NyEncoding.MULH_I, vsreg1 * vsreg2, self.vector_registers[regNo][laneNo]))))),
					ila.ite(self.rrType == self.model.const(0b010, 3),
						ila.ite(mask[laneNo] == self.model.const(0b0, 1), self.vector_registers[regNo][laneNo], 
							ila.ite(self.rrOpcode == NyEncoding.ADD_I, vsreg1 + ssreg2,
							ila.ite(self.rrOpcode == NyEncoding.SUB_I, vsreg1 - ssreg2,
							ila.ite(self.rrOpcode == NyEncoding.AND, vsreg1 & ssreg2, 
							ila.ite(self.rrOpcode == NyEncoding.OR, vsreg1 | ssreg2, 
							ila.ite(self.rrOpcode == NyEncoding.MULH_I, vsreg1 * ssreg2, self.vector_registers[regNo][laneNo])))))),
					ila.ite(self.rrType == self.model.const(0b101, 3),
							ila.ite(mask[laneNo] == self.model.const(0b0, 1), self.vector_registers[regNo][laneNo], 
							ila.ite(self.rrOpcode == NyEncoding.ADD_I, vsreg1 + vsreg2,
							ila.ite(self.rrOpcode == NyEncoding.SUB_I, vsreg1 - vsreg2,
							ila.ite(self.rrOpcode == NyEncoding.AND, vsreg1 & vsreg2, 
							ila.ite(self.rrOpcode == NyEncoding.OR, vsreg1 | vsreg2, 
							ila.ite(self.rrOpcode == NyEncoding.MULH_I, vsreg1 * vsreg2, self.vector_registers[regNo][laneNo])))))),
						self.vector_registers[regNo][laneNo])
					))),
				ila.ite(self.isImmediate,
					ila.ite(self.immType == self.model.const(0b01, 2),
						ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.ADD_I, vsreg1 + self.immB,
						ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.SUB_I, vsreg1 - self.immB,
						ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.AND, vsreg1 & self.immB,
						ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.OR, vsreg1 | self.immB,
						ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.MULH_I, vsreg1 * self.immB,
						self.vector_registers[regNo][laneNo]))))),
					ila.ite(self.immType == self.model.const(0b11, 2),
						ila.ite(mask[laneNo] == self.model.const(0b0, 1), self.vector_registers[regNo][laneNo], 
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.ADD_I, vsreg1 + self.immA, 
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.SUB_I, vsreg1 - self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.AND, vsreg1 & self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.OR, vsreg1 | self.immA,
							ila.ite(ila.zero_extend(self.immOpcode, 6) == NyEncoding.MULH_I, vsreg1 * self.immA, 
							self.vector_registers[regNo][laneNo])))))),
						self.vector_registers[regNo][laneNo]),
					),
				ila.ite(self.isLoad == self.model.const(0b1, 1), self.vector_registers[regNo][laneNo], self.vector_registers[regNo][laneNo])
				)),
			 self.vector_registers[regNo][laneNo])
				



		# return ila.choice('reg_' + str(regNo) + '_' + str(laneNo) + '_nxt',\
  #   		[self.vector_registers[regNo][laneNo], ila.ite((regNo == self.rrDest) & (fmt != self.model.const(0b000, 3)),
  #   	ila.choice('reg_' + str(regNo) + '_' + str(laneNo) + '_nxt',\
  #   	 [dest,\
  #   	  sreg1 | sreg2,\
  #   	  sreg1 & sreg2,\
  #   	  sreg1 ^ sreg2,\
  #   	  sreg1 + sreg2,\
  #   	  sreg1 - sreg2,\
  #   	  sreg1 * sreg2
    	  # (ila.zero_extend(sreg1, 64) * ila.zero_extend(sreg2, 64))[63:31],\
    	  # ila.ashr(sreg1, sreg2[4:0]),\
    	  # sreg1 >> sreg2[4:0],\
    	  # sreg1 << sreg2[4:0],\
    	  # self.aux_clz(sreg2),\
    	  # self.aux_ctz(sreg2),\
    	  # ila.ite(laneNo == -1, dest, self.indexToVGPR(self.rrSrc1, sreg2)),\
    	  # sreg2,\
    	  # (sreg1 == sreg2),\
    	  # (sreg1 != sreg2),\
    	  # (sreg1 > sreg2),\
    	  # (sreg1 >= sreg2),\
    	  # (sreg1 < sreg2),\
    	  # (sreg1 <= sreg2),\
    	  # sreg1 | self.imm,\
    	  # sreg1 & self.imm,\
    	  # sreg1 ^ self.imm,\
    	  # sreg1 + self.imm,\
    	  # sreg1 - self.imm,\
    	  # sreg1 * self.imm,\
    	  # (ila.zero_extend(sreg1, 64) * ila.zero_extend(self.imm, 64))[63:31],\
    	  # ila.ashr(sreg1, self.imm[4:0]),\
    	  # sreg1 >> self.imm[4:0],\
    	  # sreg1 << self.imm[4:0],\
    	  # self.aux_clz(self.imm),\
    	  # self.aux_ctz(self.imm),\
    	  # ila.ite(laneNo == -1, dest, self.indexToVGPR(self.rrSrc1, self.imm)),\
    	  # self.imm,\
    	  # ila.zero_extend(load_val[7:0], SCALAR_REG_BITS),\
    	  # ila.zero_extend(load_val[15:0], SCALAR_REG_BITS),\
    	  # ila.sign_extend(load_val[7:0], SCALAR_REG_BITS),\
    	  # ila.sign_extend(load_val[15:0], SCALAR_REG_BITS),\
    	  # load_val
#    	  ]), self.vector_registers[regNo][laneNo])])

	def mem_nxt(self, laneNo = -1):
		sreg1 = self.indexToSGPR(self.memSrc)
		sreg2 = self.indexToSGPR(self.memPtr)
    	#sreg1 = ila.ite(self.memOpcode == self.model.const(4b0111, 4), self.indexToVGPR(self.memSrc, laneNo), ila.ite(self.memOpcode == self.model.const(4b1000, 4), self.indexToVGPR(self.memSrc, laneNo), self.sreg1))
		addr = sreg2 + self.memOffSet
		addr2 = sreg2 + self.memOffSet + laneNo * 4
		return self.mem
		#return ila.choice("mem_next", 
    		#[self.model.mem, 
    		#ila.store(self.model.mem, addr, sreg1[7:0]), ila.store(self.model.mem, addr, sreg1[15:0]), ila.store(self.model.mem, addr, sreg1), ila.store(self.model.mem, addr2, sreg1[7:0]), ila.store(self.model.mem, addr2, sreg1[15:0]), ila.store(self.model.mem, addr2, sreg1)
    		#])
	
	def aux_clz(self, data):
		counter = self.model.const(0b0, SCALAR_REG_BITS)
		flag = self.model.const(0b0, 1)
		for idx in xrange(SCALAR_REG_BITS):
 			counter = ila.ite(flag == self.model.const(0b0, 1), ila.ite(data[idx] == self.model.const(0b0, 1), counter + 1, counter), counter)
			flag = ila.ite(flag == self.model.const(0b1, 1), flag, ila.ite(data[idx] == self.model.const(0b0, 1), flag, self.model.const(0b0, 1)))
		return counter

	def auz_ctz(self, data):
		counter = self.model.const(0b0, SCALAR_REG_BITS)
		flag = self.model.const(0b0, 1)
		for idx in xrange(SCALAR_REG_BITS)[::-1]:
 			counter = ila.ite(flag == self.model.const(0b0, 1), ila.ite(data[idx] == self.model.const(0b0, 1), counter + 1, counter), counter)
			flag = ila.ite(flag == self.model.const(0b1, 1), flag, ila.ite(data[idx] == self.model.const(0b0, 1), flag, self.model.const(0b0, 1)))
		return counter

	def addInstruction(self):
		self.aluInstruction = [(self.isRegReg) & (self.rrOpcode == NyEncoding.OR),\
		(self.isRegReg) & (self.rrOpcode == NyEncoding.AND),\
		(self.isRegReg) & (self.rrOpcode == NyEncoding.XOR),\
    	(self.isRegReg) & (self.rrOpcode == NyEncoding.ADD_I),\
    	(self.isRegReg) & (self.rrOpcode == NyEncoding.SUB_I),\
    	(self.isRegReg) & (self.rrOpcode == NyEncoding.MULH_I)]

    def auxMull_i(self, dataA, dataB):				
    	dataAIsNeg = dataA[31]
    	dataBIsNeg = dataB[31]
    	#First calculate whether the result is positive/negative
    	resultIsNeg = dataAIsNeg ^ dataBIsNeg
    	absDataA = ila.ite(dataAIsNeg, (~dataA) + self.model.const(0b1, SCALAR_REG_BITS), dataA)
    	absDataB = ila.ite(dataBIsNeg, (~dataB) + self.model.const(0b1, SCALAR_REG_BITS), dataB)
    	#Zero-extend the data to multiply
        absDataADoubleLength = ila.zero_extend(absDataA, 2 * SCALAR_REG_BITS)
        absDataBDoubleLength = ila.zero_extend(absDataB, 2 * SCALAR_REG_BITS)
    	absResultDoubleLength = absDataADoubleLength * absDataBDoubleLength
    	#Adjust the pos/neg of the result
    	resultDoubleLength = ila.ite(resultIsNeg, (~absResultDoubleLength) + 1, absResultDoubleLength)
    	mulResult = resultDoubleLength[SCALAR_REG_BITS - 1:0]
    	return mulResult

    def auxMulh_u(self, dataA, dataB):	#unsigned mul
    	dataADoubleLength = ila.zero_extend(dataA, 2 * SCALAR_REG_BITS)
    	dataBDoubleLength = ila.zero_extend(dataB, 2 * SCALAR_REG_BITS)
    	resultDoubleLength = dataADoubleLength * dataBDoubleLength
    	mulResult = resultDoubleLength[31:0]
    	return mulResult
    def getConstZero(self, length = 1):
    	return self.model.const(0b0, length)
    def getConstOne(self, length = 1):
    	return self.model.const(0b1, length)

    def auxCmpgt_i(self, dataA, dataB):	#return ila.const(1/0,1bit)
    	dataAIsNeg = dataA[31]
    	dataBIsNeg = dataB[31]
    	absDataA = ila.ite(dataAIsNeg, (~dataA) + self.getConstOne(SCALAR_REG_BITS), dataA)
    	absDataB = ila.ite(dataBIsNeg, (~dataB) + self.getConstOne(SCALAR_REG_BITS), dataB)

    	return ila.ite((dataAIsNeg == self.getConstOne()) & (dataBIsNeg == self.getConstZero()), self.getConstZero(), 
    		   ila.ite((dataAIsNeg == self.getConstZero()) & (dataBIsNeg == self.getConstOne()), self.getConstOne(), 
    		   ila.ite(dataAIsNeg == self.getConstZero(), 
    		   	ila.ite(absDataA > absDataB, self.getConstOne(), self.getConstZero()), 
    		   	ila.ite(absDataA < absDataB, self.getConstOne(), self.getConstZero()))))

    def auxCompge_i(self, dataA, dataB):
     	dataAIsNeg = dataA[31]
    	dataBIsNeg = dataB[31]
    	absDataA = ila.ite(dataAIsNeg, (~dataA) + self.getConstOne(SCALAR_REG_BITS), dataA)
    	absDataB = ila.ite(dataBIsNeg, (~dataB) + self.getConstOne(SCALAR_REG_BITS), dataB)

    	return ila.ite((dataAIsNeg == self.getConstOne()) & (dataBIsNeg == self.getConstZero()), self.getConstZero(), 
    		   ila.ite((dataAIsNeg == self.getConstZero()) & (dataBIsNeg == self.getConstOne()), self.getConstOne(), 
    		   ila.ite(dataAIsNeg == self.getConstZero(), 
    		   	ila.ite(absDataA < absDataB, self.getConstZero(), self.getConstOne()), 
    		   	ila.ite(absDataA > absDataB, self.getConstZero(), self.getConstOne()))))  

    def auxCmplt_i(self, dataA, dataB):
    	dataAIsNeg = dataA[31]
    	dataBIsNeg = dataB[31]
    	absDataA = ila.ite(dataAIsNeg, (~dataA) + self.getConstOne(SCALAR_REG_BITS), dataA)
    	absDataB = ila.ite(dataBIsNeg, (~dataB) + self.getConstOne(SCALAR_REG_BITS), dataB)

    	return ila.ite((dataAIsNeg == self.getConstOne()) & (dataBIsNeg == self.getConstZero()), self.getConstOne(), 
    		   ila.ite((dataAIsNeg == self.getConstZero()) & (dataBIsNeg == self.getConstOne()), self.getConstZero(), 
    		   ila.ite(dataAIsNeg == self.getConstZero(), 
    		   	ila.ite(absDataA < absDataB, self.getConstOne(), self.getConstZero()), 
    		   	ila.ite(absDataA > absDataB, self.getConstOne(), self.getConstZero()))))

    def auxCmple_i(self, dataA, dataB):
    	dataAIsNeg = dataA[31]
    	dataBIsNeg = dataB[31]
    	absDataA = ila.ite(dataAIsNeg, (~dataA) + self.getConstOne(SCALAR_REG_BITS), dataA)
    	absDataB = ila.ite(dataBIsNeg, (~dataB) + self.getConstOne(SCALAR_REG_BITS), dataB)

    	return ila.ite((dataAIsNeg == self.getConstOne()) & (dataBIsNeg == self.getConstZero()), self.getConstOne(), 
    		   ila.ite((dataAIsNeg == self.getConstZero()) & (dataBIsNeg == self.getConstOne()), self.getConstZero(), 
    		   ila.ite(dataAIsNeg == self.getConstZero(), 
    		   	ila.ite(absDataA > absDataB, self.getConstZero(), self.getConstOne()), 
    		   	ila.ite(absDataA < absDataB, self.getConstZero(), self.getConstOne()))))