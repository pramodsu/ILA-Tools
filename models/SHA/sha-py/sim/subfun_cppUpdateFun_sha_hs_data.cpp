#include "common.hpp"
#include "model_sha_class.hpp"

BIT_VEC model_sha::cppUpdateFun_sha_hs_data(BIT_VEC cmd, BIT_VEC cmdaddr, BIT_VEC cmddata)
{
	BIT_VEC cppVar_1768;
	bool cppVar_1770 = (sha_state == 3);
	bool cppVar_1772 = (cmd != 1);
	bool cppVar_1773 = cppVar_1770 && cppVar_1772;
	bool cppVar_1775 = (cmdaddr == 65039);
	bool cppVar_1776 = cppVar_1773 && cppVar_1775;
	bool cppVar_1778 = (sha_state == 3);
	bool cppVar_1780 = (cmd != 1);
	bool cppVar_1781 = cppVar_1778 && cppVar_1780;
	bool cppVar_1783 = (cmdaddr == 65038);
	bool cppVar_1784 = cppVar_1781 && cppVar_1783;
	bool cppVar_1786 = (sha_state == 3);
	bool cppVar_1788 = (cmd != 1);
	bool cppVar_1789 = cppVar_1786 && cppVar_1788;
	bool cppVar_1791 = (cmdaddr == 65037);
	bool cppVar_1792 = cppVar_1789 && cppVar_1791;
	bool cppVar_1794 = (sha_state == 3);
	bool cppVar_1796 = (cmd != 1);
	bool cppVar_1797 = cppVar_1794 && cppVar_1796;
	bool cppVar_1799 = (cmdaddr == 65036);
	bool cppVar_1800 = cppVar_1797 && cppVar_1799;
	bool cppVar_1802 = (sha_state == 3);
	bool cppVar_1804 = (cmd != 1);
	bool cppVar_1805 = cppVar_1802 && cppVar_1804;
	bool cppVar_1807 = (cmdaddr == 65035);
	bool cppVar_1808 = cppVar_1805 && cppVar_1807;
	bool cppVar_1810 = (sha_state == 3);
	bool cppVar_1812 = (cmd != 1);
	bool cppVar_1813 = cppVar_1810 && cppVar_1812;
	bool cppVar_1815 = (cmdaddr == 65034);
	bool cppVar_1816 = cppVar_1813 && cppVar_1815;
	bool cppVar_1818 = (sha_state == 3);
	bool cppVar_1820 = (cmd != 1);
	bool cppVar_1821 = cppVar_1818 && cppVar_1820;
	bool cppVar_1823 = (cmdaddr == 65033);
	bool cppVar_1824 = cppVar_1821 && cppVar_1823;
	bool cppVar_1826 = (sha_state == 3);
	bool cppVar_1828 = (cmd != 1);
	bool cppVar_1829 = cppVar_1826 && cppVar_1828;
	bool cppVar_1831 = (cmdaddr == 65032);
	bool cppVar_1832 = cppVar_1829 && cppVar_1831;
	bool cppVar_1834 = (sha_state == 3);
	bool cppVar_1836 = (cmd != 1);
	bool cppVar_1837 = cppVar_1834 && cppVar_1836;
	bool cppVar_1839 = (cmdaddr == 65031);
	bool cppVar_1840 = cppVar_1837 && cppVar_1839;
	bool cppVar_1842 = (sha_state == 3);
	bool cppVar_1844 = (cmd != 1);
	bool cppVar_1845 = cppVar_1842 && cppVar_1844;
	bool cppVar_1847 = (cmdaddr == 65030);
	bool cppVar_1848 = cppVar_1845 && cppVar_1847;
	bool cppVar_1850 = (sha_state == 3);
	bool cppVar_1852 = (cmd != 1);
	bool cppVar_1853 = cppVar_1850 && cppVar_1852;
	bool cppVar_1855 = (cmdaddr == 65029);
	bool cppVar_1856 = cppVar_1853 && cppVar_1855;
	bool cppVar_1858 = (sha_state == 3);
	bool cppVar_1860 = (cmd != 1);
	bool cppVar_1861 = cppVar_1858 && cppVar_1860;
	bool cppVar_1863 = (cmdaddr == 65028);
	bool cppVar_1864 = cppVar_1861 && cppVar_1863;
	bool cppVar_1866 = (sha_state == 3);
	bool cppVar_1868 = (cmd != 1);
	bool cppVar_1869 = cppVar_1866 && cppVar_1868;
	bool cppVar_1871 = (cmdaddr == 65027);
	bool cppVar_1872 = cppVar_1869 && cppVar_1871;
	bool cppVar_1874 = (sha_state == 3);
	bool cppVar_1876 = (cmd != 1);
	bool cppVar_1877 = cppVar_1874 && cppVar_1876;
	bool cppVar_1879 = (cmdaddr == 65026);
	bool cppVar_1880 = cppVar_1877 && cppVar_1879;
	bool cppVar_1882 = (sha_state == 3);
	bool cppVar_1884 = (cmd != 1);
	bool cppVar_1885 = cppVar_1882 && cppVar_1884;
	bool cppVar_1887 = (cmdaddr == 65025);
	bool cppVar_1888 = cppVar_1885 && cppVar_1887;
	bool cppVar_1890 = (sha_state == 3);
	bool cppVar_1892 = (cmd != 1);
	bool cppVar_1893 = cppVar_1890 && cppVar_1892;
	bool cppVar_1895 = (cmdaddr == 65024);
	bool cppVar_1896 = cppVar_1893 && cppVar_1895;
	bool cppVar_1898 = (sha_state == 3);
	bool cppVar_1900 = (cmd == 1);
	bool cppVar_1901 = cppVar_1898 && cppVar_1900;
	bool cppVar_1903 = (cmdaddr == 65039);
	bool cppVar_1904 = cppVar_1901 && cppVar_1903;
	bool cppVar_1906 = (sha_state == 3);
	bool cppVar_1908 = (cmd == 1);
	bool cppVar_1909 = cppVar_1906 && cppVar_1908;
	bool cppVar_1911 = (cmdaddr == 65038);
	bool cppVar_1912 = cppVar_1909 && cppVar_1911;
	bool cppVar_1914 = (sha_state == 3);
	bool cppVar_1916 = (cmd == 1);
	bool cppVar_1917 = cppVar_1914 && cppVar_1916;
	bool cppVar_1919 = (cmdaddr == 65037);
	bool cppVar_1920 = cppVar_1917 && cppVar_1919;
	bool cppVar_1922 = (sha_state == 3);
	bool cppVar_1924 = (cmd == 1);
	bool cppVar_1925 = cppVar_1922 && cppVar_1924;
	bool cppVar_1927 = (cmdaddr == 65036);
	bool cppVar_1928 = cppVar_1925 && cppVar_1927;
	bool cppVar_1930 = (sha_state == 3);
	bool cppVar_1932 = (cmd == 1);
	bool cppVar_1933 = cppVar_1930 && cppVar_1932;
	bool cppVar_1935 = (cmdaddr == 65035);
	bool cppVar_1936 = cppVar_1933 && cppVar_1935;
	bool cppVar_1938 = (sha_state == 3);
	bool cppVar_1940 = (cmd == 1);
	bool cppVar_1941 = cppVar_1938 && cppVar_1940;
	bool cppVar_1943 = (cmdaddr == 65034);
	bool cppVar_1944 = cppVar_1941 && cppVar_1943;
	bool cppVar_1946 = (sha_state == 3);
	bool cppVar_1948 = (cmd == 1);
	bool cppVar_1949 = cppVar_1946 && cppVar_1948;
	bool cppVar_1951 = (cmdaddr == 65033);
	bool cppVar_1952 = cppVar_1949 && cppVar_1951;
	bool cppVar_1954 = (sha_state == 3);
	bool cppVar_1956 = (cmd == 1);
	bool cppVar_1957 = cppVar_1954 && cppVar_1956;
	bool cppVar_1959 = (cmdaddr == 65032);
	bool cppVar_1960 = cppVar_1957 && cppVar_1959;
	bool cppVar_1962 = (sha_state == 3);
	bool cppVar_1964 = (cmd == 1);
	bool cppVar_1965 = cppVar_1962 && cppVar_1964;
	bool cppVar_1967 = (cmdaddr == 65031);
	bool cppVar_1968 = cppVar_1965 && cppVar_1967;
	bool cppVar_1970 = (sha_state == 3);
	bool cppVar_1972 = (cmd == 1);
	bool cppVar_1973 = cppVar_1970 && cppVar_1972;
	bool cppVar_1975 = (cmdaddr == 65030);
	bool cppVar_1976 = cppVar_1973 && cppVar_1975;
	bool cppVar_1978 = (sha_state == 3);
	bool cppVar_1980 = (cmd == 1);
	bool cppVar_1981 = cppVar_1978 && cppVar_1980;
	bool cppVar_1983 = (cmdaddr == 65029);
	bool cppVar_1984 = cppVar_1981 && cppVar_1983;
	bool cppVar_1986 = (sha_state == 3);
	bool cppVar_1988 = (cmd == 1);
	bool cppVar_1989 = cppVar_1986 && cppVar_1988;
	bool cppVar_1991 = (cmdaddr == 65028);
	bool cppVar_1992 = cppVar_1989 && cppVar_1991;
	bool cppVar_1994 = (sha_state == 3);
	bool cppVar_1996 = (cmd == 1);
	bool cppVar_1997 = cppVar_1994 && cppVar_1996;
	bool cppVar_1999 = (cmdaddr == 65027);
	bool cppVar_2000 = cppVar_1997 && cppVar_1999;
	bool cppVar_2002 = (sha_state == 3);
	bool cppVar_2004 = (cmd == 1);
	bool cppVar_2005 = cppVar_2002 && cppVar_2004;
	bool cppVar_2007 = (cmdaddr == 65026);
	bool cppVar_2008 = cppVar_2005 && cppVar_2007;
	bool cppVar_2010 = (sha_state == 3);
	bool cppVar_2012 = (cmd == 1);
	bool cppVar_2013 = cppVar_2010 && cppVar_2012;
	bool cppVar_2015 = (cmdaddr == 65025);
	bool cppVar_2016 = cppVar_2013 && cppVar_2015;
	bool cppVar_2018 = (sha_state == 3);
	bool cppVar_2020 = (cmd == 1);
	bool cppVar_2021 = cppVar_2018 && cppVar_2020;
	bool cppVar_2023 = (cmdaddr == 65024);
	bool cppVar_2024 = cppVar_2021 && cppVar_2023;
	bool cppVar_2025 = cppVar_2016 || cppVar_2024;
	bool cppVar_2026 = cppVar_2008 || cppVar_2025;
	bool cppVar_2027 = cppVar_2000 || cppVar_2026;
	bool cppVar_2028 = cppVar_1992 || cppVar_2027;
	bool cppVar_2029 = cppVar_1984 || cppVar_2028;
	bool cppVar_2030 = cppVar_1976 || cppVar_2029;
	bool cppVar_2031 = cppVar_1968 || cppVar_2030;
	bool cppVar_2032 = cppVar_1960 || cppVar_2031;
	bool cppVar_2033 = cppVar_1952 || cppVar_2032;
	bool cppVar_2034 = cppVar_1944 || cppVar_2033;
	bool cppVar_2035 = cppVar_1936 || cppVar_2034;
	bool cppVar_2036 = cppVar_1928 || cppVar_2035;
	bool cppVar_2037 = cppVar_1920 || cppVar_2036;
	bool cppVar_2038 = cppVar_1912 || cppVar_2037;
	bool cppVar_2039 = cppVar_1904 || cppVar_2038;
	bool cppVar_2040 = cppVar_1896 || cppVar_2039;
	bool cppVar_2041 = cppVar_1888 || cppVar_2040;
	bool cppVar_2042 = cppVar_1880 || cppVar_2041;
	bool cppVar_2043 = cppVar_1872 || cppVar_2042;
	bool cppVar_2044 = cppVar_1864 || cppVar_2043;
	bool cppVar_2045 = cppVar_1856 || cppVar_2044;
	bool cppVar_2046 = cppVar_1848 || cppVar_2045;
	bool cppVar_2047 = cppVar_1840 || cppVar_2046;
	bool cppVar_2048 = cppVar_1832 || cppVar_2047;
	bool cppVar_2049 = cppVar_1824 || cppVar_2048;
	bool cppVar_2050 = cppVar_1816 || cppVar_2049;
	bool cppVar_2051 = cppVar_1808 || cppVar_2050;
	bool cppVar_2052 = cppVar_1800 || cppVar_2051;
	bool cppVar_2053 = cppVar_1792 || cppVar_2052;
	bool cppVar_2054 = cppVar_1784 || cppVar_2053;
	bool cppVar_2055 = cppVar_1776 || cppVar_2054;
	if (cppVar_2055) {
	BIT_VEC cppVar_2056 = sha(sha_rd_data);
	cppVar_1768 = cppVar_2056;
	} else {
	cppVar_1768 = sha_hs_data;
	}
	return cppVar_1768;
}
