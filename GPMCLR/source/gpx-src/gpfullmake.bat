@echo off
REM
REM assemble all files of gpx and gpmx
REM
gpx -c m2object.def m2clrcod.def m2clrtre.def m2treeto.def m2alphab.def m2nameha.def m2nodede.def m2tabini.def m2sympar.def m2inout.def m2scanne.def m2design.def m2traver.def m2machin.def m2parser.def m2struct.def m2reffil.def m2dcfwrappers.def m2cilwrappers.def m2ssutil.def m2ddefin.def m2dwrite.def m2rtsint.def m2procst.def m2namgen.def m2litcha.def m2il.def m2cilwriter.def m2settem.def m2gdbsup.def m2compop.def m2casese.def m2exppar.def safe.def

gpx -cg m2object.mod m2clrcod.mod m2clrtre.mod m2treeto.mod m2tabini.mod m2sympar.mod m2inout.mod m2scanne.mod m2nameha.mod m2traver.mod m2nodede.mod m2machin.mod m2parser.mod m2alphab.mod m2design.mod m2struct.mod m2reffil.mod m2dcfwrappers.mod m2cilwrappers.mod m2ssutil.mod m2dwrite.mod m2ddefin.mod m2rtsint.mod m2procst.mod m2namgen.mod m2litcha.mod m2il.mod m2cilwriter.mod m2settem.mod m2gdbsup.mod m2compop.mod m2casese.mod m2exppar.mod safe.mod 

gpx -cgS gpmx.mod
gpx -cgS gpx.mod
ilasm /exe /debug /quiet gpx.il
ilasm /exe /debug /quiet gpmx.il

move *.exe ..\..\M2ClrBin
move *.dll ..\..\M2ClrBin
move *.pdb ..\..\M2ClrBin

