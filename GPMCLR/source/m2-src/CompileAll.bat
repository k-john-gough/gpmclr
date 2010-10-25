@echo off
gpx /cg AsciiTime.mod buildargs.mod cardsequences.mod cardtrees.mod charinfo.mod convtypes.mod gensequencesupport.mod gpfiles.mod pathlookup.mod random.mod realconv.mod realinout.mod realstr.mod stdstrings.mod strings.mod wholestr.mod             
move *.dll ..\..\M2ClrBin
move *.pdb ..\..\M2ClrBin

