//  
//  Bootstrap library for gpmd-CLR
//  Piggybacks on System.Console.
//  
//  
using System;

namespace StdError {

  public unsafe class StdError {

    public static void WriteLn() {
       System.Console.Error.WriteLine();
    }

    public static void Write(byte chr) {
       System.Console.Error.Write((char)chr);
    }

    public static void WriteString(byte* ptr, uint lim) {
       uint idx;
       char chr;
       for (idx = 0; idx <= lim; idx++) {
         chr = (char)(*(ptr+idx));
         if (chr == (char)0) return;
         System.Console.Error.Write(chr);
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
                System.Console.Error.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Error.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Error.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Error.Write(buf[indx]);
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
                System.Console.Error.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Error.Write(buf[indx]);
        } else {                    // some blank space padding
            for (indx = 0; indx < (fld-wdth); indx++)
                System.Console.Error.Write(' ');
            for (indx = iMsd; indx < 12; indx++)
                System.Console.Error.Write(buf[indx]);
        }
    }

  }
}
