#
#	initially generated by c2l
#

Ar: module
{
	PATH: con "ar.dis";

	ARMAG: con "!<arch>\n";
	SARMAG: con 8;
	ARFMAG: con "`\n";
	SARNAME: con 16;

	ar_hdr: adt{
		name: array of byte;	#  SARNAME
		date: array of byte;	#  12
		uid: array of byte;	#  6
		gid: array of byte;	#  6
		mode: array of byte;	#  8
		size: array of byte;	#  10
		fmag: array of byte;	#  2
	};

	SAR_HDR: con 60;

};