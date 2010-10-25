
(* ==================================================== *)
(*  Implementation  automatically produced by MkEnumIO  *)
(* ==================================================== *)

IMPLEMENTATION MODULE TermSymbolsIO;

  IMPORT InOut, TextInOut, UxFiles;
  FROM MkAlphabets IMPORT TermSymbols;
  FROM ConvTypes IMPORT ConvResults;

  CONST tMx = 605;

  TYPE Index = ARRAY TermSymbols OF CARDINAL;
       StTab = ARRAY [0 .. tMx] OF CHAR;

  CONST enumStart = Index{
	0, 6, 12, 18, 23, 29, 35, 41, 46, 52, 
	57, 64, 70, 78, 86, 91, 98, 103, 109, 114, 
	119, 125, 131, 138, 145, 151, 156, 160, 166, 173, 
	177, 185, 194, 203, 209, 219, 224, 233, 242, 249, 
	254, 266, 274, 281, 286, 291, 298, 306, 313, 320, 
	327, 336, 344, 352, 357, 364, 370, 379, 385, 393, 
	400, 413, 430, 436, 442, 454, 463, 469, 477, 487, 
	494, 503, 511, 519, 525, 535, 541, 551, 561, 570, 
	580, 588, 597
    }; (* compile errors here mean that type 'TermSymbols'
	* has changed its cardinality since module 'TermSymbolsIO'
	* was created. Rerun MkEnumIO to fix this module	*)

  CONST stringTab = StTab{
	"e","r","r","S","y","",
	"a","n","d","S","y","",
	"d","i","v","S","y","",
	"s","t","a","r","",
	"s","l","a","s","h","",
	"m","o","d","S","y","",
	"r","e","m","S","y","",
	"p","l","u","s","",
	"m","i","n","u","s","",
	"o","r","S","y","",
	"e","q","u","a","l","s","",
	"n","o","t","E","q","",
	"g","r","e","a","t","e","r","",
	"g","r","E","q","u","a","l","",
	"l","e","s","s","",
	"l","e","s","s","E","q","",
	"i","n","S","y","",
	"n","o","t","S","y","",
	"l","P","a","r","",
	"r","P","a","r","",
	"l","B","r","a","c","",
	"r","B","r","a","c","",
	"l","C","u","r","l","y","",
	"r","C","u","r","l","y","",
	"c","o","m","m","a","",
	"s","e","m","i","",
	"d","o","t","",
	"c","o","l","o","n","",
	"d","o","t","D","o","t","",
	"b","a","r","",
	"u","p","A","r","r","o","w","",
	"a","s","s","i","g","n","S","y","",
	"r","e","c","o","r","d","S","y","",
	"s","e","t","S","y","",
	"p","o","i","n","t","e","r","S","y","",
	"t","o","S","y","",
	"i","m","p","o","r","t","S","y","",
	"e","x","p","o","r","t","S","y","",
	"f","r","o","m","S","y","",
	"o","f","S","y","",
	"q","u","a","l","i","f","i","e","d","S","y","",
	"b","e","g","i","n","S","y","",
	"c","a","s","e","S","y","",
	"b","y","S","y","",
	"i","f","S","y","",
	"t","h","e","n","S","y","",
	"e","l","s","i","f","S","y","",
	"e","l","s","e","S","y","",
	"l","o","o","p","S","y","",
	"e","x","i","t","S","y","",
	"r","e","p","e","a","t","S","y","",
	"u","n","t","i","l","S","y","",
	"w","h","i","l","e","S","y","",
	"d","o","S","y","",
	"w","i","t","h","S","y","",
	"f","o","r","S","y","",
	"r","e","t","u","r","n","S","y","",
	"e","n","d","S","y","",
	"c","o","n","s","t","S","y","",
	"t","y","p","e","S","y","",
	"d","e","f","i","n","i","t","i","o","n","S","y","",
	"i","m","p","l","e","m","e","n","t","a","t","i","o","n","S","y","",
	"v","a","r","S","y","",
	"n","i","l","S","y","",
	"p","r","o","c","e","d","u","r","e","S","y","",
	"m","o","d","u","l","e","S","y","",
	"i","d","e","n","t","",
	"a","r","r","a","y","S","y","",
	"l","i","t","s","t","r","i","n","g","",
	"f","i","x","N","u","m","",
	"f","l","o","a","t","N","u","m","",
	"c","h","a","r","L","i","t","",
	"c","h","a","r","N","u","m","",
	"k","e","y","S","y","",
	"b","i","g","S","e","t","C","o","n","",
	"e","o","f","S","y","",
	"f","o","r","w","a","r","d","S","y","",
	"h","e","a","p","C","o","n","s","t","",
	"s","t","r","i","n","g","S","y","",
	"f","i","n","a","l","l","y","S","y","",
	"r","e","t","r","y","S","y","",
	"e","x","c","e","p","t","S","y","",
	"p","r","e","c","o","n","S","y",""};

  PROCEDURE Write(val : TermSymbols);
    VAR strng : ARRAY [0 .. 255] OF CHAR;
  BEGIN
    GiveStr(val,strng);
    InOut.WriteString(strng);
  END Write;

  PROCEDURE TextWrite(fil : UxFiles.File;
                      val : TermSymbols);
    VAR strng : ARRAY [0 .. 255] OF CHAR;
  BEGIN
    GiveStr(val,strng);
    TextInOut.WriteString(fil,strng);
  END TextWrite;

  PROCEDURE GiveStr(val : TermSymbols;
               VAR str : ARRAY OF CHAR);
    VAR index : CARDINAL;
        strIx : CARDINAL;
  BEGIN
    strIx := 0;
    index := enumStart[val];
    WHILE (stringTab[index] <> '') AND
               (strIx <= HIGH(str)) DO
      str[strIx] := stringTab[index];
      INC(index); INC(strIx);
    END;
    IF strIx <= HIGH(str) THEN str[strIx] := '' END;
  END GiveStr;

END TermSymbolsIO.
