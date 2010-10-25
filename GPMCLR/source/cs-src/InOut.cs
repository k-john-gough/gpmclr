//  
//  Bootstrap library for gpmd-CLR
//  Piggybacks on System.Console.
//  
//  
using System;

namespace InOut {

  public unsafe class InOut {

// ==================================================================

    public  static byte termCh  = (byte)0;
    public  static byte Done    = 0;
    private static bool eofRead = false;

    // -----------------------------------------------
    public static void OpenInput(byte* ptr, uint lim) {
        // not implemented yet ...
        Done = 0; // false
        throw new Exception("OpenInput not implemented");
    }

    // -----------------------------------------------
    public static void OpenOutput(byte* ptr, uint lim) {
        // not implemented yet ...
        Done = 0; // false
        throw new Exception("OpenOutput not implemented");
    }

    // -----------------------------------------------
    public static void CloseInput() {
        throw new Exception("CloseInput not implemented");
        // not implemented yet ...
    }

    // -----------------------------------------------
    public static void CloseOutput() {
        throw new Exception("CloseOutput not implemented");
        // not implemented yet ...
    }

    // -----------------------------------------------
    public static void Read(byte* chr) {
        int nxt = System.Console.Read();
        if (nxt == -1) {
            Done = 0;
            eofRead = true;
        } else {
            Done = 1;
            *chr = (byte)nxt;
        }
    }

    // -----------------------------------------------
    public static void ReadLn() {
        string str = System.Console.ReadLine();
        if (str == null) {
            Done = 0;
            eofRead = true;
        } else
            Done = 1;
    }

    // -----------------------------------------------
    public static void ReadString(byte* str, uint max) {
        int  nxt;
        uint idx = 0;
        //
        //  Check for empty stream
        //
        if (eofRead) {
            Done = 0;
            return;                                // premature exit here
        }
        //
        //  Skip white space
        //
        do {
            nxt = System.Console.Read();
        } while (nxt == ' ' || nxt == '\t');
        *str = (byte)nxt;
        //
        //  Check for end-of-input
        //
        if (nxt == -1) {
            eofRead = true;
            termCh  = (byte)nxt;
            Done    = 0;
            return;                                // premature exit here
        } else
            idx++;
        //
        //  Get rest of bytes
        //
        for (;;) {
            nxt = System.Console.Read();
            if (nxt <= (int)' ') {
                if (nxt == -1) {
                    Done = 0;
                    eofRead = true;
                } else 
                    Done = 1;
                if (idx < max)
                    *(str + idx) = (byte)0;
                termCh = (byte)nxt;
                return;                            // premature exit here
            } else {
                if (idx < max)
                    *(str + idx) = (byte)nxt;
                idx++;
            }
        }
    }

    // -----------------------------------------------
    public static void ReadCard(uint* crd) {
        uint tmp = 0;
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
            if (nxt <= '9' && nxt >= '0') {
                Done = 1;
                tmp  = ((uint)nxt - (uint)'0');
                nxt  = System.Console.Read();
                while (nxt <= '9' && nxt >= '0') {
                    tmp = checked(tmp * 10 + ((uint)nxt - (uint)'0'));
                    nxt = System.Console.Read();
                } 
            }
            termCh = (byte)nxt;
            *crd = tmp;
            if (nxt == -1)
                eofRead = true;
        } catch {
            Done = 0;
            *crd = 0;
        }
        // throw new Exception("ReadCard not implemented");
    }

    // -----------------------------------------------
    public static void ReadInt(int* val) {
        int  tmp = 0;
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
               tmp  = ((int)nxt - (int)'0');
               nxt  = System.Console.Read();
               while (nxt <= '9' && nxt >= '0') {
                   tmp = checked(tmp * 10 + ((int)nxt - (int)'0'));
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



// ==================================================================
    public static void WriteLn() {
       System.Console.WriteLine();
    }

    public static void Write(byte chr) {
       System.Console.Write((char)chr);
    }

    public static void WriteString(byte* ptr, uint lim) {
       uint idx;
       char chr;
       for (idx = 0; idx <= lim; idx++) {
         chr = (char)(*(ptr+idx));
         if (chr == (char)0) return;
         System.Console.Write(chr);
       }
    }

    public static void WriteCard(uint crd, uint fld) {
        char[] buf = new char[12];
        int indx = 12;
        int iMsd;
        int wdth;
        //  post-tested loop so that 0 prints as "0"
        do {
            indx--;
            buf[indx] = (char)((int)(crd % 10) + (int)'0');
            crd /= (uint)10;
        } while (crd > 0);
        iMsd = indx;
        wdth = 12-iMsd;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        }
    }

    public static void WriteInt(int num, uint fld) {
        char[] buf = new char[12];
        int  indx = 12;
        int  iMsd;
        int  wdth;
        uint crd;
        bool ngtv = (num < 0);
        if (ngtv)
            num = -num;
        crd = (uint)num;
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
        iMsd = indx;
        wdth = 12-iMsd;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        }
    }

    public static void WriteOct(uint crd, uint fld) {
        char[] buf = new char[16];
        int indx = 16;
        int iMsd;
        int wdth;
        //  post-tested loop so that 0 prints as "0"
        do {
            indx--;
            buf[indx] = (char)((int)(crd % 8) + (int)'0');
            crd /= (uint)8;
        } while (crd > 0);
        iMsd = indx;
        wdth = 16-iMsd;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 16; indx++)
                System.Console.Write(buf[indx]);
        }
    }

    public static void WriteHex(uint crd, uint fld) {
        char[] buf = new char[12];
        int indx = 12;
        int hxDg;
        int hxCh;
        int iMsd;
        int wdth;
        //  post-tested loop so that 0 prints as "0"
        do {
            indx--;
            hxDg = (int)(crd % 16);
            hxCh = (hxDg < 10 ? hxDg + (int)'0' : hxDg + (int)'a' - 10);
            buf[indx] = (char)hxCh;
            crd /= (uint)16;
        } while (crd > 0);
        iMsd = indx;
        wdth = 12-iMsd;
        //
        //   012345678901
        //  "     ddddddd"
        //        ^ ... iMsd
        //
        if (fld <= wdth) {          // just the significant digits
            if (fld == 0)           // mandatory leading blank
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Write(buf[indx]);
        }
    }

  }
}
