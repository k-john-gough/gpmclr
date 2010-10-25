/****************************************************************)
(*                                                              *)
(*    High level input and output procedures for HUGEINTS	*)
(*                                                              *)
(*       modifications   : kjg September 1995	 	        *)
(*                                                              *)
(****************************************************************/
//  
//  Bootstrap library for gpmd-CLR
//  Piggybacks on System.Console and TextInOut
//  
//  
using System;
using TextInOut;

namespace HugeInOut {

  public unsafe class HugeInOut {


// -----------------------------------------------------------------

    public  static byte termCh  = (byte)0;
    public  static byte Done    = 0;
    private static bool eofRead = false;

// -----------------------------------------------------------------

    // -----------------------------------------------
    // Precondition  : TRUE
    // Postcondition : Done = TRUE if and only if the next sequence of 
    //                   characters on the input stream represents a
    //                   HUGEINT value. The variable termCh is set to the
    //                   value of the character that terminates this 
    //                   sequence.  
    // -----------------------------------------------
    //   PROCEDURE ReadInt    (VAR n: HUGEINT);
    // -----------------------------------------------
    public static void ReadInt(long* val) {
        long tmp = 0;
        bool ngt = false;
        int  nxt;
        Done = 0;
        //
        //  Check for empty stream
        //
        if (eofRead)
            return;                                // premature exit here
        //
        //  Skip white space
        //
        do {
            nxt = System.Console.Read();
        } while (nxt <= ' ');
        try {
            if (nxt == '-') {
                ngt = true; nxt = System.Console.Read();
            } else if (nxt == '+')
                nxt = System.Console.Read();
            if (nxt <= '9' && nxt >= '0') {
                Done = 1;
                tmp  = (long)(nxt - (int)'0');
                nxt  = System.Console.Read();
                while (nxt <= '9' && nxt >= '0') {
                    tmp = checked(tmp * 10 + (long)(nxt - (int)'0'));
                    nxt = System.Console.Read();
                } 
            }
            if (ngt)
                tmp = -tmp;
            termCh = (byte)nxt;
            *val = tmp;
            if (nxt == -1)
                eofRead = true;
        } catch {
            Done = 0;
            *val = 0;
        }
        // throw new Exception("ReadInt not implemented");
    }

    // -----------------------------------------------
    //   PROCEDURE TextReadInt(f : File; VAR n : HUGEINT);
    // -----------------------------------------------
    public static void TextReadInt(void* f, long* n) {
        long tmp = 0;
        bool ngt = false;
        byte nxt;

        Done = 0;
        //
        //  Skip white space
        //
        do {
            TextInOut.TextInOut.Read(f, &nxt);
            if (TextInOut.TextInOut.Done == 0) return;  // premature exit here
        } while (nxt <= ' ');
        try {
            if (nxt == (byte)'-') {
                ngt = true; 
                TextInOut.TextInOut.Read(f, &nxt);
                if (TextInOut.TextInOut.Done == 0) 
                    nxt = (byte)0;
            } else if (nxt == (byte)'+')
                TextInOut.TextInOut.Read(f, &nxt);
            if (nxt <= (byte)'9' && nxt >= (byte)'0') {
                Done = 1;
                tmp  = (long)(nxt - (int)'0');
                TextInOut.TextInOut.Read(f, &nxt);
                if (TextInOut.TextInOut.Done == 0) 
                    nxt = (byte)0;
                while (nxt <= (byte)'9' && nxt >= (byte)'0') {
                    tmp = checked(tmp * 10 + (long)(nxt - (int)'0'));
                    TextInOut.TextInOut.Read(f, &nxt);
                    if (TextInOut.TextInOut.Done == 0) 
                        nxt = (byte)0;
                } 
            }
            if (ngt)
                tmp = -tmp;
            termCh = nxt;
            *n = tmp;
        } catch {
            Done = 0;
            *n = 0;
        }
        // throw new Exception("TextReadInt not implemented");
    }
    
    // -----------------------------------------------
    //   PROCEDURE StrReadInt(s : ARRAY OF CHAR; VAR n : HUGEINT);
    // -----------------------------------------------
    public static void StrReadInt(byte* s, uint sHi, long* n) {
        long tmp = 0;
        bool ngt = false;
        uint idx = 0;
        int  nxt;

        Done = 0;
        //
        //  Skip white space
        //
        for ( ; ; ) {
            if (idx > sHi) nxt = -1; else nxt = *(s+idx++);
            if (nxt < 0 || nxt > ' ')
                break;
        }
        try {
            if (nxt == '-' || nxt == '+') {
                ngt = (nxt == '-'); 
                if (idx > sHi) nxt = -1; else nxt = *(s+idx++);
            }
            if (nxt <= '9' && nxt >= '0') {
                Done = 1;
                tmp  = (long)(nxt - (int)'0'); 
                if (idx > sHi) nxt = -1; else nxt = *(s+idx++);
                while (nxt <= (byte)'9' && nxt >= (byte)'0') {
                    tmp = checked(tmp * 10 + (long)(nxt - (int)'0'));
                    if (idx > sHi) nxt = -1; else nxt = *(s+idx++);
                } 
            }
            if (ngt)
                tmp = -tmp;
            termCh = (byte)nxt;
            *n = tmp;
        } catch {
            Done = 0;
            *n = 0;
        }
        // throw new Exception("StrReadInt not implemented");
    }
    
// -----------------------------------------------------------------
// -----------------------------------------------------------------

    private static char[] getIntStr(long num, int* msd) {
        char[] buf = new char[24];
        int   indx = 24;
        ulong crd;
        bool  ngtv = (num < 0);
        if (ngtv)
            num = -num;
        crd = (ulong)num;
        //  post-tested loop so that 0 prints as "0"
        do {
            indx--;
            buf[indx] = (char)((int)(crd % 10) + (int)'0');
            crd /= 10;
        } while (crd > 0);
        if (ngtv) {
            indx--;
            buf[indx] = '-';
        }
        *msd = indx;
        return buf;
    }

// -----------------------------------------------------------------

    private static char[] getOctStr(long num, int* msd) {
        char[] buf = new char[24];
        int   indx = 24;
        ulong crd;
        crd = (ulong)num;
        //  post-tested loop so that 0 prints as "0"
        do {
            indx--;
            buf[indx] = (char)((int)(crd % 8) + (int)'0');
            crd /= 8;
        } while (crd > 0);
        *msd = indx;
        return buf;
    }

// -----------------------------------------------------------------

    private static char[] getHexStr(long num, int* msd) {
        char[] buf = new char[24];
        int   indx = 24;
        int   dVal;           // digit value
        ulong crd;
        crd = (ulong)num;
        //  post-tested loop so that 0 prints as "0"
        do {
            indx--;
            dVal = (int)(crd % 16);
            dVal += (dVal >= 10 ? ((int)'a'-10) : (int)'0');
            buf[indx] = (char)dVal;
            crd /= 16;
        } while (crd > 0);
        *msd = indx;
        return buf;
    }

// -----------------------------------------------------------------
// -----------------------------------------------------------------

    // -----------------------------------------------
    //    PROCEDURE WriteInt(num : HUGEINT; wid : CARDINAL);
    // -----------------------------------------------
    public static void WriteInt(long num, uint fld) {
        int  iMsd;
        char[] buf = getIntStr(num, &iMsd);
        int  wdth = 24 - iMsd;
        int  indx;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 24; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 24; indx++)
                System.Console.Write(buf[indx]);
        }
    }

    // -----------------------------------------------
    //    PROCEDURE TextWriteInt(fil : File; num : HUGEINT; wid : CARDINAL);
    // -----------------------------------------------
    public static void TextWriteInt(void* fil,
                                    long  num, 
                                    uint  fld) {
        int  iMsd;
        char[] buf = getIntStr(num, &iMsd);
        int  wdth  = 24 - iMsd;
        int  indx;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                TextInOut.TextInOut.Write(fil, (byte)' ');
            for (indx = iMsd; indx < 24; indx++)
                TextInOut.TextInOut.Write(fil, (byte)buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                TextInOut.TextInOut.Write(fil, (byte)' ');
            for (indx = iMsd; indx < 24; indx++)
                TextInOut.TextInOut.Write(fil, (byte)buf[indx]);
        }
    }
 
    // -----------------------------------------------
    //    PROCEDURE StrWriteInt (num : HUGEINT; 
    //                           wid : CARDINAL;
    //                       VAR out : ARRAY OF CHAR);
    // -----------------------------------------------
    public static void StrWriteInt(long  num, 
                                   uint  fld,
                                   byte* str,
                                   uint  hSt) {
        int  iMsd;
        char[] buf = getIntStr(num, &iMsd);
        int  wdth  = 24 - iMsd;
        int  indx;

        if (hSt < wdth) {
            wdth = (int)hSt;
            for (int i = 0; i < hSt; i++) buf[i] = '*';
        }

        if (fld <= wdth) {          // just the significant digits
            indx = 0;
            if (fld == 0) {         // mandatory leading blank
                *(str + indx) = (byte)' '; indx++;
            }
            for (int i = iMsd; i < 24; i++, indx++) {
                *(str + indx) = (byte)buf[i]; indx++;
            }
        } else {                    // some blank space padding
            indx = 0;
            while (indx < (fld-wdth)) {
                *(str + indx) = (byte)' '; indx++;
            }
            for (int i = iMsd; i < 24; i++, indx++) {
                *(str + indx) = (byte)buf[i];
            }
        }
    }
 
// -----------------------------------------------------------------
// -----------------------------------------------------------------

    // -----------------------------------------------
    //    PROCEDURE WriteOct    (num : HUGEINT; wid : CARDINAL);
    // -----------------------------------------------
 
    public static void WriteOct (long num, uint fld) {
        int  iMsd;
        char[] buf = getOctStr(num, &iMsd);
        int  wdth = 24 - iMsd;
        int  indx;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 24; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 24; indx++)
                System.Console.Write(buf[indx]);
        }
    }

    // -----------------------------------------------
    //    PROCEDURE TextWriteOct(fil : File; num : HUGEINT; wid : CARDINAL);
    // -----------------------------------------------
    public static void TextWriteOct(void* fil,
                                    long  num, 
                                    uint  fld) {
        int  iMsd;
        char[] buf = getOctStr(num, &iMsd);
        int  wdth  = 24 - iMsd;
        int  indx;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                TextInOut.TextInOut.Write(fil, (byte)' ');
            for (indx = iMsd; indx < 24; indx++)
                TextInOut.TextInOut.Write(fil, (byte)buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                TextInOut.TextInOut.Write(fil, (byte)' ');
            for (indx = iMsd; indx < 24; indx++)
                TextInOut.TextInOut.Write(fil, (byte)buf[indx]);
        }
    }
 
    // -----------------------------------------------
    //    PROCEDURE StrWriteOct (num : HUGEINT; 
    //                           wid : CARDINAL;
    //                       VAR out : ARRAY OF CHAR);
    // -----------------------------------------------
    public static void StrWriteOct(long  num, 
                                   uint  fld,
                                   byte* str,
                                   uint  hSt) {
        int  iMsd;
        char[] buf = getOctStr(num, &iMsd);
        int  wdth  = 24 - iMsd;
        int  indx;

        if (hSt < wdth) {
            wdth = (int)hSt;
            for (int i = 0; i < hSt; i++) buf[i] = '*';
        }

        if (fld <= wdth) {          // just the significant digits
            indx = 0;
            if (fld == 0) {         // mandatory leading blank
                *(str + indx) = (byte)' '; indx++;
            }
            for (int i = iMsd; i < 24; i++, indx++) {
                *(str + indx) = (byte)buf[i]; indx++;
            }
        } else {                    // some blank space padding
            indx = 0;
            while (indx < (fld-wdth)) {
                *(str + indx) = (byte)' '; indx++;
            }
            for (int i = iMsd; i < 24; i++, indx++) {
                *(str + indx) = (byte)buf[i];
            }
        }
    }
 
// -----------------------------------------------------------------
// -----------------------------------------------------------------

    // -----------------------------------------------
    //    PROCEDURE WriteHex    (num : HUGEINT; wid : CARDINAL);
    // -----------------------------------------------
 
    public static void WriteHex (long num, uint fld) {
        int  iMsd;
        char[] buf = getHexStr(num, &iMsd);
        int  wdth = 24 - iMsd;
        int  indx;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 24; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 24; indx++)
                System.Console.Write(buf[indx]);
        }
    }

    // -----------------------------------------------
    //    PROCEDURE TextWriteHex(fil : File; num : HUGEINT; wid : CARDINAL);
    // -----------------------------------------------
    public static void TextWriteHex(void* fil,
                                    long  num, 
                                    uint  fld) {
        int  iMsd;
        char[] buf = getHexStr(num, &iMsd);
        int  wdth  = 24 - iMsd;
        int  indx;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                TextInOut.TextInOut.Write(fil, (byte)' ');
            for (indx = iMsd; indx < 24; indx++)
                TextInOut.TextInOut.Write(fil, (byte)buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                TextInOut.TextInOut.Write(fil, (byte)' ');
            for (indx = iMsd; indx < 24; indx++)
                TextInOut.TextInOut.Write(fil, (byte)buf[indx]);
        }
    }
 
    // -----------------------------------------------
    //    PROCEDURE StrWriteHex (num : HUGEINT; 
    //                           wid : CARDINAL;
    //                       VAR out : ARRAY OF CHAR);
    // -----------------------------------------------
    public static void StrWriteHex(long  num, 
                                   uint  fld,
                                   byte* str,
                                   uint  hSt) {
        int  iMsd;
        char[] buf = getHexStr(num, &iMsd);
        int  wdth  = 24 - iMsd;
        int  indx;

        if (hSt < wdth) {
            wdth = (int)hSt;
            for (int i = 0; i < hSt; i++) buf[i] = '*';
        }

        if (fld <= wdth) {          // just the significant digits
            indx = 0;
            if (fld == 0) {         // mandatory leading blank
                *(str + indx) = (byte)' '; indx++;
            }
            for (int i = iMsd; i < 24; i++, indx++) {
                *(str + indx) = (byte)buf[i]; indx++;
            }
        } else {                    // some blank space padding
            indx = 0;
            while (indx < (fld-wdth)) {
                *(str + indx) = (byte)' '; indx++;
            }
            for (int i = iMsd; i < 24; i++, indx++) {
                *(str + indx) = (byte)buf[i];
            }
        }
    }
 
// -----------------------------------------------------------------
// -----------------------------------------------------------------
    }  // End of class HugeInOut
}  // End of namespace HugeInOut
// -----------------------------------------------------------------
// -----------------------------------------------------------------

