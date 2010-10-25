
/***********************************************************************)
(*                                                                     *)
(*              Modula-2 Compiler TextInOut Library Module             *)
(*                                                                     *)
(*          High level input and output procedures for                 *)
(*          characters, strings, integers and cardinals                *)
(*                                                                     *)
(*       THIS MODULE PROVIDES THE SAME PROCEDURES AS InOut	       *)
(*	 BUT USES NAMED FILES AS SOURCE AND DESTINATION		       *)
(*								       *)
(*       original module : N. Wirth, PIM-2,  1982 (InOut)              *)
(*       modifications   : 					       *)
(*                                                                     *)
(***********************************************************************/

using System;
using UxFiles;
using System.Runtime.InteropServices;

namespace TextInOut
{
    public unsafe class TextInOut
    {

      private  const  int  FAIL    = -1;
      private  const  byte mTrue   = (byte) 1;
      private  const  byte mFalse  = (byte) 0;
      private  const  byte uEOF    = (byte) 255;
      private  const  uint maxU10  = 429496729;   // maxcard DIV 10
      private  const  int  maxS10  = 214748364;   // maxint  DIV 10

      public  static byte termCh  = (byte)0;
      public  static byte Done    = 0;

    // =====================================================================
    //  PROCEDURE Read(inFile : File; VAR c:CHAR);
    //  (* Precondition  : TRUE
    //     Postcondition : Done = FALSE if and only if the end of the primary
    //                     input stream is reached, otherwise c is the next 
    //                     character in the stream.  *)
    // =====================================================================

        public static void Read(void* fil, byte* chr) {
            int iVar;
            if (feof(fil) != 0)
                Done = mFalse;
            else {
                if ((iVar = fgetc(fil)) == FAIL) {
                    Done = mFalse;
                    *chr = (byte) 0;
                } else {
                    Done = mTrue;
                    *chr = (byte) iVar;
                }
            }
        }

    // =====================================================================
    //  PROCEDURE ReadString(inFile : File; VAR s: ARRAY OF CHAR);
    //  (* Precondition  : TRUE
    //     Postcondition : Inputs a character string from the primary input
    //                     stream until any character less than or equal to 
    //                     a blank is read. The variable termCh is set to the
    //                     value of this terminating character. 
    //                     The NUL character (0C) or the end of the array is
    //                     used to mark the end of the string.
    //                     Leading blanks and/or tabs are ignored. Excess 
    //                     characters beyond the length of s are discarded. *)
    // =====================================================================

        public static void ReadString(void* fil, byte* str, uint high) {
            int iVar;
            int indx;
            if (feof(fil) != 0)
                Done = mFalse;
            else {
                // skip leading white space ...
                while ((iVar = fgetc(fil)) == (int)' ' || iVar == (int)'\t')
                    ;
                *str = (byte) iVar; indx = 0;
                if (iVar == FAIL) {
                    termCh = (byte) 0;
                } else {
                    // read until blank or control character or indx == high
                    while (indx < high && iVar > (int) ' ') {
                        indx++;
                        iVar = fgetc(fil);
                        *(str+indx) = (byte) iVar;
                    }
                    // test reason for exit
                    if (indx == high) {
                        while (iVar > (int) ' ') {
                            iVar = fgetc(fil);
                        }
                    } else {        // short string ...
                        indx++;
                        *(str+indx) = (byte) 0;
                    }
                    if (iVar == FAIL)
                        termCh = (byte) 0;
                    else
                        termCh = (byte) iVar;
                    Done = mTrue;
                }
            }
        }

    // =====================================================================
    //  PROCEDURE ReadCard(inFile : File; VAR n: CARDINAL);
    //  (* Precondition  : TRUE
    //     Postcondition : Done = TRUE if and only if the next sequence of 
    //                     characters on the input stream represents a
    //                     CARDINAL value. The variable termCh is set to the
    //                     value of the character that terminates this 
    //                     sequence.  *)
    // =====================================================================

        public static void ReadCard(void* file, uint* rslt) {
            byte noOvf;
            uint nd, nn;
            int  iVar;

            noOvf = mTrue;
            if (feof(file) != 0)
                Done = mFalse;
            else {
                // skip leading white space ...
                while ((iVar = fgetc(file)) == (int)' ' || iVar == (int)'\t') 
                    ;
                if (iVar >= (int) '0' && iVar <= (int) '9') {
                    nd = 0;
                    do {
                        nn = nd * 10 + (uint)(iVar - (int) ' ');
                        // inline overflow test
                        if (nd > maxU10 || nn < nd)
                            noOvf = mFalse;
                        iVar = fgetc(file);
                        nd = nn;
                    } while (iVar >= (int) '0' && iVar <= (int) '9');
                    *rslt  = nd;
                    Done   = noOvf;
                    termCh = (byte) iVar;
                } else {  // a non-digit has been found
                    Done   = mFalse;
                    termCh = (byte) iVar;
                }
            }
        }

    // =====================================================================
    //  PROCEDURE ReadInt(inFile : File; VAR i : INTEGER);
    //  (* Precondition  : TRUE
    //     Postcondition : Done = TRUE if and only if the next sequence of 
    //                     characters on the input stream represents a
    //                     INTEGER value. The variable termCh is set to the
    //                     value of the character that terminates this 
    //                     sequence.  *)
    // =====================================================================

        public static void ReadInt(void* file, int* rslt) {
            byte noOvf;
            int  nd, nn;
            int  iVar;
            bool isNeg = false;

            noOvf = mTrue;
            if (feof(file) != 0)
                Done = mFalse;
            else {
                // skip leading white space ...
                while ((iVar = fgetc(file)) == (int)' ' || iVar == (int)'\t') 
                    ;
                if (iVar == (int) '+' || iVar == (int) '-') {
                    isNeg = iVar == (int) '-';
                    iVar  = fgetc(file);
                }
                if (iVar >= (int) '0' && iVar <= (int) '9') {
                    nd = 0;
                    do {
                        nn = nd * 10 + (iVar - (int) ' ');
                        // inline overflow test
                        if (nd > maxS10 || nn < nd)
                            noOvf = mFalse;
                        iVar = fgetc(file);
                        nd = nn;
                    } while (iVar >= (int) '0' && iVar <= (int) '9');
                    if (isNeg) {
                        nd = -nd;
                        if (nd < 0)
                            noOvf = mFalse;
                    } 
                    *rslt  = nd;
                    Done   = noOvf;
                    termCh = (byte) iVar;
                } else {  // a non-digit has been found
                    Done   = mFalse;
                    termCh = (byte) iVar;
                }
            }
        }

    // =====================================================================
    //  PROCEDURE Write(outFile : File; c:CHAR);
    //  (* Precondition  : c is defined.
    //     Postcondition : The character representation corresponding to the
    //                     value of c is written to the output stream.  *)
    // =====================================================================

        public static void Write(void* file, byte chr) {
            fputc(chr & 255, file);
        }

    // =====================================================================
    //  PROCEDURE WriteLn(outFile : File); 
    //    (* Precondition  : TRUE
    //       Postcondition : Equivalent to Write(EOL).  *)
    // =====================================================================

        public static void WriteLn(void* file) {
            fputc('\n', file);
        }

    // =====================================================================
    //  PROCEDURE WriteString(outFile : File; s : ARRAY OF CHAR);
    //  (* Precondition  : s is defined.
    //     Postcondition : Outputs a string of characters until a NUL character
    //                     or the end of the array is encountered.  *)
    // =====================================================================

        public static void WriteString(void* file, 
                                       byte* chrs,
                                       uint  high) {
            int indx;
            int chrI;
            for (indx = 0; indx <= high; indx++ ) {
                chrI = ((int) *(chrs+indx)) & 255; // extend to int, mask off
                if (chrI == 0)
                     return;
                fputc(chrI, file);
            }
        }

    // =====================================================================
    //  PROCEDURE WriteCard(outFile : File; n: CARDINAL; w: CARDINAL);
    //  (* Precondition  : n and w are defined.
    //     Postcondition : The value of n is written to the output stream
    //                     occupying at least w character positions. Leading
    //                     blanks fill out the space if it is not all required.
    //                     The decimal number system is used.  *)
    // =====================================================================

        public static void WriteCard(void* file, uint valu, uint fWid) {

            int[] buf = new int[12];
            int indx = 12;
            int iMsd;
            int wdth;

            if (fWid > 256)
                fWid = 256;

            //  post-tested loop so that 0 prints as "0"
            do {
                indx--;
                buf[indx] = ((int)(valu % 10) + (int)'0');
                valu /= (uint)10;
            } while (valu > 0);
            iMsd = indx;
            wdth = 12-iMsd;
            //
            //   012345678901
            //  "     ddddddd"
            //        ^ ... iMsd
            //
            if (fWid <= wdth) {          // just the significant digits
                if (fWid == 0)           // mandatory leading blank
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            } else {                    // some blank space padding
                for (indx = 0; indx < (fWid-wdth); indx++)
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            }
        }

    // =====================================================================
    //  PROCEDURE WriteInt(outFile : File; i: INTEGER; w: CARDINAL);
    //  (* Precondition  : i and w are defined.
    //     Postcondition : The value of i is written to the output stream
    //                     occupying at least w character positions. Leading
    //                     blanks fill out the space if it is not all required.
    //                     The decimal number system is used and a sign is 
    //                     displayed only for negative numbers.  *)
    // =====================================================================

        public static void WriteInt(void* file, int valu, uint fWid) {

            int[] buf = new int[12];
            int  indx = 12;
            int  iMsd;
            int  wdth;
            uint crd;
            bool ngtv = (valu < 0);

            if (fWid > 256)
                fWid = 256;

            if (ngtv)
                crd = (uint)(-valu);
            else
                crd = (uint) valu;

            //  post-tested loop so that 0 prints as "0"
            do {
                indx--;
                buf[indx] = ((int)(crd % 10) + (int)'0');
                crd /= 10;
            } while (crd > 0);

            if (ngtv) {
                indx--;
                buf[indx] = (int)'-';
            }

            iMsd = indx;
            wdth = 12-iMsd;
            //
            //   012345678901
            //  "     ddddddd"
            //        ^ ... iMsd
            //
            if (fWid <= wdth) {          // just the significant digits
                if (fWid == 0)           // mandatory leading blank
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            } else {                    // some blank space padding
                for (indx = 0; indx < (fWid-wdth); indx++)
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            }
        }

    // =====================================================================
    //  PROCEDURE WriteOct(outFile : File; n: CARDINAL; w: CARDINAL);
    //  (* Precondition  : n and w are defined.
    //     Postcondition : The value of n is written to the output stream
    //                     occupying at least w character positions. Leading
    //                     blanks fill out the space if it is not all required.
    //                     The octal number system is used.  *)
    // =====================================================================

        public static void WriteOct(void* file, uint valu, uint fWid) {

            int[] buf = new int[12];
            int indx = 12;
            int iMsd;
            int wdth;

            if (fWid > 256)
                fWid = 256;

            //  post-tested loop so that 0 prints as "0"
            do {
                indx--;
                buf[indx] = ((int)(valu % 8) + (int)'0');
                valu /= (uint)8;
            } while (valu > 0);
            iMsd = indx;
            wdth = 12-iMsd;
            //
            //   012345678901
            //  "     ddddddd"
            //        ^ ... iMsd
            //
            if (fWid <= wdth) {          // just the significant digits
                if (fWid == 0)           // mandatory leading blank
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            } else {                    // some blank space padding
                for (indx = 0; indx < (fWid-wdth); indx++)
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            }
        }

    // =====================================================================
    //  PROCEDURE WriteHex(outFile : File; n: CARDINAL; w: CARDINAL);
    //  (* Precondition  : n and w are defined.
    //     Postcondition : The value of n is written to the output stream
    //                     occupying at least w character positions. Leading
    //                     blanks fill out the space if it is not all required.
    //                     The hexadecimal number system is used.  *)
    // =====================================================================

        public static void WriteHex(void* file, uint valu, uint fWid) {

            int[] buf = new int[12];
            int indx = 12;
            int iMsd;
            int wdth;
            int digt;

            if (fWid > 256)
                fWid = 256;

            //  post-tested loop so that 0 prints as "0"
            do {
                indx--;
                digt = (int)(valu % 16);
                if (digt < 10)
                    buf[indx] = digt + (int)'0';
                else
                    buf[indx] = digt + ((int)'a' - 10);
                valu /= (uint)16;
            } while (valu > 0);
            iMsd = indx;
            wdth = 12-iMsd;
            //
            //   012345678901
            //  "     ddddddd"
            //        ^ ... iMsd
            //
            if (fWid <= wdth) {          // just the significant digits
                if (fWid == 0)           // mandatory leading blank
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            } else {                    // some blank space padding
                for (indx = 0; indx < (fWid-wdth); indx++)
                    fputc(' ', file);
                for (indx = iMsd; indx < 12; indx++)
                    fputc(buf[indx] & 255, file);
            }
        }

    // =====================================================================

    [DllImport("msvcrt")]
    static extern int fgetc(void* file);
    
    [DllImport("msvcrt")]
    static extern int fputc(int c, void* file);
    
    [DllImport("msvcrt")]
    static extern int feof(void* file);

    // =====================================================================
    }
}
// =====================================================================
