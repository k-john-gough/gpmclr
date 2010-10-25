//
// Interoperation files for GPM-CLR
// Implementation of modules: Storage, UxFiles
// kjg October 2003
//
// ----------------------------------------------------------------------
using System;
using System.IO;
using System.Text;
using System.Runtime.InteropServices;
// ----------------------------------------------------------------------
//
// FOREIGN DEFINITION MODULE Storage;
//   IMPORT IMPLEMENTATION FROM "m2iop";
//
//  FROM SYSTEM IMPORT ADDRESS;
//
//  PROCEDURE ALLOCATE(VAR ptr : ADDRESS; size : CARDINAL);
//  (* postcondition : returns a ptr to object of size bytes   *)
//  (*                 rounded up to a whole number of words   *)
//
//  PROCEDURE DEALLOCATE(VAR ptr : ADDRESS; size : CARDINAL);
//  (* precondition  : ptr^ must have been gained from heap    *)
//  (* postcondition : (pre-ptr)^ is disposed, ptr = NIL       *)
//
//END Storage.
//

namespace Storage {
    public unsafe class Storage
    {
        private Storage() { }

        public static void ALLOCATE(void** dst, uint size) {
            void* tmp = malloc((int) size);
            *dst = tmp;
        }

        public static void DEALLOCATE(void** dst, uint size) {
            free(*dst); 
            *dst = null;
        }

    [DllImport("msvcrt")]
    static extern void* malloc(int siz);

    [DllImport("msvcrt")]
    static extern void free(void* ptr);
    
    }
}
// ----------------------------------------------------------------------
//
//  UxFiles implementation for gpm-CLR
//
// ----------------------------------------------------------------------

namespace UxFiles {

    public enum OpenMode : byte {
         ReadOnly, WriteOnly, ReadWrite   // more for windows?
    }

    public enum FilePermissionBits : byte {
        ox, ow, or, gx, gw, gr, // unused in this implementation
        ux,                     // or 0x0040
        uw,                     // or 0x0080 
        ur,                     // or 0x0100
        x,y,z,                  // unused in this implementation
        isPipe,                 // or 0x1000
        isChSpec,               // or 0x2000
        isDir,                  // or 0x4000
        isReg}                  // or 0x8000

// ----------------------------------------------------------------------

  public unsafe class UxFiles {

    private UxFiles() { }

// ----------------------------------------------------------------------
//  TYPE
//    File;
//    OpenMode = (ReadOnly, WriteOnly, ReadWrite, 
//                ReadOnlyText, WriteOnlyText, ReadWriteText);
//
//    FilePermissionBits = 
//               (rdOnly, hidden, system, volId, subDir, archive);
//
//    FileMode   = SET OF FilePermissionBits;
//    FileAttrib = FilePermissionBits;     (* synonyms for the WildCards *)
//    FileAttSet = FileMode;               (* library                    *) 
//
//
//
//END UxFiles.
// ----------------------------------------------------------------------

    static byte[] fm  = {(byte) 'r',
                         (byte) '\0',
                         (byte) 'w',
                         (byte) '\0',
                         (byte) 'r',
                         (byte) '+',
                         (byte) '\0'};

    static byte[] wfm = {(byte) 'r',   // offset  0
                         (byte) 'b',
                         (byte) '\0',
                         (byte) 'w',   // offset  3
                         (byte) 'b',
                         (byte) '\0',
                         (byte) 'r',   // offset  6
                         (byte) '+',
                         (byte) 'b',
                         (byte) '\0',
                         (byte) 'r',   // offset 10
                         (byte) 't',
                         (byte) '\0',
                         (byte) 'w',   // offset 13
                         (byte) 't',
                         (byte) '\0',
                         (byte) 'w',   // offset 16
                         (byte) '+',
                         (byte) 't',
                         (byte) '\0'};

    public const int FAIL = -1;

    public const ushort S_IFMT   = 0xF000;  // file type mask
    public const ushort S_IFREG  = 0x8000;  // regular file
    public const ushort S_IFDIR  = 0x4000;  // directory
    public const ushort S_IFCHR  = 0x2000;  // character special
    public const ushort S_IFIFO  = 0x1000;  // pipe
    public const ushort S_IREAD  = 0x0100;  // read permission
    public const ushort S_IWRITE = 0x0080;  // write permission
    public const ushort S_IEXEC  = 0x0040;  // execute/search permission

// ----------------------------------------------------------------------

        internal static System.String mkStr(byte* arr) {
            StringBuilder bld = new StringBuilder(20);  
            int ix = 0;
            char chr = (char) *(arr+ix); ix++;
            while (chr != '\0') {
                bld.Append(chr);
                chr = (char) *(arr+ix); ix++;
            } 
            return bld.ToString();
        }

        internal static void MkArr(byte* dst, uint hiD, string arg) {
            char   chr;
            if (arg == null) {
                *dst = (byte)0;
            } else {
                int    len = arg.Length;
                for (int i = 0; i <= hiD; i++) {
                    if (i == hiD) {
                        *(dst+hiD) = (byte)0; return;
                    } else if (i == len) {
                        *(dst+len) = (byte)0; return;
                    }
                    chr = arg[i];
                    *(dst+i) = (byte)chr;
                }
            }
        }

//  ========================================================================
//  PROCEDURE Open(VAR  f: File;       (* Open an existing file *)
//                   name: ARRAY OF CHAR;
//                   mode: OpenMode;
//               VAR done: BOOLEAN);
//  ========================================================================
    public static void Open(void**     f,
                            byte*      name,
                            uint       high,
                            OpenMode   mode,
                            byte*      done) 
    {
        // Stringlength check here?
        int idx = 0;
        switch (mode) {
             case (OpenMode.ReadOnly)   : idx = 0; break;
             case (OpenMode.WriteOnly)  : idx = 3; break;
             case (OpenMode.ReadWrite)  : idx = 6; break;
        }
        *(name+high) = (byte) 0; // ensure string terminated
        fixed (byte* mPtr = &wfm[idx]) *f = (stdc_iob*) fopen(name, mPtr);
        *done = (*f == null ? (byte) 0 : (byte) 1);
    }

//  ========================================================================
//  PROCEDURE Create(VAR f: File;     (* Open a new file *)
//                    name: ARRAY OF CHAR;
//                VAR done: BOOLEAN);
//  ========================================================================
    public static void Create(void** file,
                              byte*  name,
                              uint   high,
                              byte*  done)
    {
        *(name+high) = (byte) 0; // ensure string terminated
        fixed (byte* mPtr = &wfm[3]) *file = (stdc_iob*) fopen(name, mPtr);
        *done = (*file == null ? (byte) 0 : (byte) 1);
    }

//  ========================================================================
//  PROCEDURE Close(VAR f   : File;   (* Close a file *)
//                  VAR done: BOOLEAN);
//  ========================================================================
    public static void Close(void** file, 
                             byte*  done)
    {
         if (*file != null) {
             *done = ((fclose((void*)(*file)) != FAIL) ? (byte) 1 : (byte) 0);
         } else {
             *done = (byte) 1;
         }
         *file = null;
    }

//  ========================================================================
//  PROCEDURE Delete(str : ARRAY OF CHAR;
//               VAR ok  : BOOLEAN);
//  ========================================================================
    public static void Delete(byte* name,
                              uint  high,
                              byte* done)
    {
        *done = (_unlink(name) != FAIL ? (byte) 1 : (byte) 0);
    }

//  ========================================================================
//  PROCEDURE Reset(f: File);
//(* Position the file at the beginning and set to "ReadMode"   *)
//  ========================================================================
    public static void Reset(void* file)
    {
        rewind(file);
    }

//  ========================================================================
//  PROCEDURE ReadByte(f: File;      (* Read a byte from file *)
//                 VAR b: BYTE);
//  ========================================================================
    public static void ReadByte(void*  file, 
                                sbyte* chr)   // BYTE == sbyte in C#
    {
        *chr = (sbyte)fgetc(file);
    }

//  ========================================================================
//  PROCEDURE WriteByte(f: File;      (* Write a byte to file *)
//                      b: BYTE);
//  ========================================================================
    public static void WriteByte(void* file, sbyte chr) 
    {
        fputc(chr & 255, file);
    }

//  ========================================================================
//  PROCEDURE ReadNBytes(file: File;
//                       bPtr: ADDRESS;
//                       want: CARDINAL;
//                   VAR read: CARDINAL);
//  (* Read requested bytes into buffer at address *)
//  (* 'bPtr', number of effectively read bytes    *)
//  (* is returned in 'read'                       *)
//  ========================================================================
    public static void ReadNBytes(void* file,
                                  void* bPtr,
                                  uint  want,
                                  uint* bGot)
    {
        *bGot = (uint)fread(bPtr, 1, (int)want, file);
    }

//  ========================================================================
//  PROCEDURE WriteNBytes(file: File;
//                        bPtr: ADDRESS;
//                        want: CARDINAL;
//                    VAR bPut: CARDINAL);
//  (* Write requested bytes from buffer at address *)
//  (* 'bPtr', number of effectively written bytes  *)
//  (* is returned in 'bPut'                        *)
//  ========================================================================
    public static void WriteNBytes(void* file,
                                   void* bPtr,
                                   uint  want,
                                   uint* bPut)
    {
        *bPut = (uint)fwrite(bPtr, 1, (int)want, file);
    }

//  ========================================================================
//  PROCEDURE EndFile( f : File) : BOOLEAN;
//  (* returns true if an attempt has been made
//     to read past the physical end of file   *)
//  ========================================================================
    public static byte EndFile (void* file)
    {
        return (feof(file) != 0 ? (byte) 1 : (byte) 0);
    }

//  ========================================================================
//  PROCEDURE GetPos(file : File;
//               VAR posn : CARDINAL);
//  ========================================================================
    public static void GetPos(void* file,
                              uint* posn)
    {
        *posn = (uint)ftell(file);
    }


//  ========================================================================
//  PROCEDURE SetPos(file : File;
//                   posn : CARDINAL);
//  ========================================================================
    public static void SetPos(void* file,
                              uint  posn)
    {
        fseek(file, (int)posn, 0); // position relative to the start of file
    }

//  ========================================================================
//  PROCEDURE FileSize(name : ARRAY OF CHAR;
//                 VAR size : CARDINAL;
//                 VAR ok   : BOOLEAN);
//  ========================================================================
    public static void FileSize(byte* name,
                                uint  high,
                                uint* size,
                                byte* done)
    {
        stdc_stat info;
        *(name+high) = (byte) 0; // ensure string terminated
        *done = (_stat(name, (void*)&info) != FAIL ? (byte) 1 : (byte) 0);
        *size = (uint)info.st_size;
    }

//  ========================================================================
//  PROCEDURE AccessTime(path     : ARRAY OF CHAR;
//                     VAR time : CARDINAL;
//                     VAR ok   : BOOLEAN);
//  (* finds time of last access to named file *)
//  ========================================================================
    public static void AccessTime(byte* name,
                                  uint  high,
                                  uint* time,
                                  byte* done)
    {
        stdc_stat info;
        *(name+high) = (byte) 0; // ensure string terminated
        *done = (_stat(name, (void*)&info) != FAIL ? (byte) 1 : (byte) 0);
        *time = (uint)info.st_atime;
    }

//  ========================================================================
//  PROCEDURE ModifyTime(path     : ARRAY OF CHAR;
//                     VAR time : CARDINAL;
//                     VAR ok   : BOOLEAN);
//  (* finds time of last modification to file *)
//  ========================================================================
    public static void ModifyTime(byte* name,
                                  uint  high,
                                  uint* time,
                                  byte* done)
    {
        stdc_stat info;
        *(name+high) = (byte) 0; // ensure string terminated
        *done = (_stat(name, (void*)&info) != FAIL ? (byte) 1 : (byte) 0);
        *time = (uint)info.st_mtime;
    }

//  ========================================================================
//  PROCEDURE StatusTime(path     : ARRAY OF CHAR;
//                     VAR time : CARDINAL;
//                     VAR ok   : BOOLEAN);
//  (* finds time of last status change of file *)
//  ========================================================================
    public static void StatusTime(byte* name,
                                  uint  high,
                                  uint* time,
                                  byte* done)
    {
        stdc_stat info;
        *(name+high) = (byte) 0; // ensure string terminated
        *done = (_stat(name, (void*)&info) != FAIL ? (byte) 1 : (byte) 0);
        *time = (uint)info.st_ctime;
    }

//  ========================================================================
//  PROCEDURE GetMode(name : ARRAY OF CHAR;
//                VAR mode : FileMode;
//                VAR done : BOOLEAN);
//  (* precondition  : name must be a nul-terminated variable
//                     array, or a literal string.
//     postcondition : if done then mode has permission bits *)
//  ========================================================================
    public static void GetMode(byte* name,
                               uint  high,
                               int*  mode,
                               byte* done)
    {
        stdc_stat info;
        *(name+high) = (byte) 0; // ensure string terminated
        *done = (_stat(name, (void*)&info) != FAIL ? (byte) 1 : (byte) 0);
        *mode = (int) info.st_mode;
    }

//  ========================================================================
//  PROCEDURE SetMode(name : ARRAY OF CHAR;
//                    mode : FileMode;
//                VAR done : BOOLEAN);
//  (* precondition  : name must be a nul-terminated variable
//                     array,or a literal string.
//     postcondition : if done then file has permission bits *)
//  ========================================================================
    public static void SetMode(byte* name,
                               uint  high,
                               int   mode,
                               byte* done)
    {
        *(name+high) = (byte) 0; // ensure string terminated
        *done = (_chmod(name ,(mode & 0x0180)) != FAIL ? (byte) 1 : (byte) 0);
    }

//  ========================================================================
//                       DLL - imports follow
//  ========================================================================

    [DllImport("msvcrt")]
    static extern void* fopen(byte* name, byte* mode);
    
    [DllImport("msvcrt")]
    static extern int fclose(void* file);
    
    [DllImport("msvcrt")]
    static extern int fgetc(void* file);
    
    [DllImport("msvcrt")]
    static extern int fputc(int c, void* file);
    
    [DllImport("msvcrt")]
    static extern int feof(void* file);

    [DllImport("msvcrt")]
    static extern int ftell(void* file);

    [DllImport("msvcrt")]
    static extern int fseek(void* file, int posn, int mode);
    
    [DllImport("msvcrt")]
    static extern void rewind(void* file);
    
    [DllImport("msvcrt")]
    static extern int _unlink(byte* name);

    [DllImport("msvcrt")]
    static extern int fread(void* buff, int sz, int nm, void* file);

    [DllImport("msvcrt")]
    static extern int fwrite(void* buff, int sz, int nm, void* file);
    
    [DllImport("msvcrt")]
    static extern int _stat(byte* name, void* buff);
    
    [DllImport("msvcrt")]
    static extern int _chmod(byte* name, int mode);
    
// ----------------------------------------------------------------------
    }       // end of class UxFiles
// ----------------------------------------------------------------------

    public unsafe struct stdc_iob {  // file type is "stdc_iob *"
        public byte*  _ptr;
        public int    _cnt;
        public byte*  _base;
        public int    _flag;
        public int    _file;
        public int    _charbuf;
        public int    _bufsiz;
        public byte*  _tmpfname;
    }

    public unsafe struct stdc_stat { 
        public int    st_dev;
        public int    st_ino;
        public ushort st_mode;
        public short  st_nlink;
        public short  st_uid;
        public short  st_gid;
        public int    st_rdev;
        public int    st_size;
        public int    st_atime;
        public int    st_mtime;
        public int    st_ctime;
    }

// ----------------------------------------------------------------------
}           // end of namespace UxFiles
// ----------------------------------------------------------------------
namespace FLength {
    public unsafe class FLength {

        private const int SEEK_SET = 0;
        private const int SEEK_CUR = 1;
        private const int SEEK_END = 2;

//  PROCEDURE Length(f : UxFiles.File) : CARDINAL;
//  (* post : if f is open return length, else 0 *)
//
        public static uint  Length(void* f) {
            int pos, len;
            pos = ftell(f);
            fseek(f, 0, SEEK_END);
            len = ftell(f);
            fseek(f, pos, SEEK_SET);
            return ((uint)len);
        }

//  PROCEDURE SeekEnd(f : UxFiles.File; VAR ok : BOOLEAN);
//  (* post : file is postioned at end, or ok = false *)
//
        public static void SeekEnd(void* f, byte* ok) {
            int retval = fseek(f,0,SEEK_END);    /* seek to end of file   */
            *ok = (retval == -1 ? (byte)0 : (byte)1);
        }

//  PROCEDURE Rename(old, new : ARRAY OF CHAR;
//                   VAR  ok  : BOOLEAN);
//
        public static void Rename(byte* oNm, uint oNmHi,
                                  byte* nNm, uint nNmHi,
                                  byte* ok) {
            throw new Exception("Rename not implemented");
        }

    [DllImport("msvcrt")]
    static extern int ftell(void* file);

    [DllImport("msvcrt")]
    static extern int fseek(void* file, int posn, int mode);
    
    }
// ----------------------------------------------------------------------
}           // end of namespace FLength
// ----------------------------------------------------------------------
namespace DtoA {

    public unsafe class DtoA {

    public const int ERANGE = 34;
    public static int errno;

    private const byte nulB = (byte) 0;
    private static byte* buff = (byte*) malloc(32);

    // ================================================================
    // ================================================================
    // ================================================================
    //  PROCEDURE strtod(VAR str : ARRAY OF CHAR) : REAL;
    // ================================================================
    public static double strtod(byte* str, uint high) {
        *(str+high) = nulB;      // ensure string terminated
        return strtod(str, (byte**) null);
    }

    // ================================================================
    private static void Strip(byte* arr, int dpt) {
       int ix = dpt;
       int jx = dpt;
       byte chr = *(arr+ix);
       while (chr != nulB) {
           ix++;
           chr = *(arr+ix);
           //
           // Track position of '0' bytes, looking for
           // the first zero not followed by another digit.
           //
           if (chr == (byte) '0') {
               if (jx == dpt)
                   jx = ix;            // Could be first trailing '0'
           } else if (chr != nulB) {
               jx = dpt;               // Oops! Only an embedded '0'
           }
       }
       if (jx > dpt) {
           *(arr+jx) = nulB;
       }
    }

    // ================================================================
    //  PROCEDURE dtoa(d      : REAL;
    //                 mode : INTEGER;
    //                 nDig : INTEGER
    //             VAR dcPt : INTEGER;
    //             VAR sign : BOOLEAN) : ADDRESS; // pointer to buffer.
    // ================================================================
    public static void* dtoa(double val, int  mode, int   nDig, 
                                         int* dcPt, byte* sign) {
        byte* rslt;
        int   iSgn = 0;
        switch (mode) {
            case 2:   rslt = _ecvt(val, (nDig > 0 ? nDig : 0), dcPt, &iSgn); 
                      Strip(rslt, 0);
                      break;
            case 3:   rslt = _fcvt(val, nDig, dcPt, &iSgn); 
                      Strip(rslt, (*dcPt > 0 ? *dcPt : 0));
                      break;
            default : rslt = _ecvt(val, 18, dcPt, &iSgn); 
                      Strip(rslt, 0);
                      break;
        }
        if (System.Double.IsNaN(val)) {
            errno = ERANGE;
            *dcPt = 9999;
        }
        *sign = (iSgn == 0 ? (byte) 0 : (byte) 1);
        return (void*) rslt;
    }

    // ================================================================
    [DllImport("msvcrt")]
    static extern double strtod(byte* str, byte** tail);

    [DllImport("msvcrt")]
    static extern byte* _ecvt(double val, int nDig, int* decpt, int* sign);

    [DllImport("msvcrt")]
    static extern byte* _fcvt(double val, int nDig, int* decpt, int* sign);

    [DllImport("msvcrt")]
    static extern void* malloc(int siz);

    } // end class DtoA
} // end namespace DtoA
// ========================================================================

namespace Wildcards {

    public unsafe class Wildcards {

// ========================================================================
//  PROCEDURE GetMatchingFiles(dirName : ARRAY OF CHAR;
//                             pattern : ARRAY OF CHAR) : BuildArgs.ArgPtr;
// ========================================================================
        public static void* GetMatchingFiles(byte* dir, uint dHi,
                                             byte* ptn, uint pHi) 
        {
            *(dir+dHi) = (byte) 0;
            *(ptn+pHi) = (byte) 0; // ensure string terminated
            System.String dStr = UxFiles.UxFiles.mkStr(dir);
            System.String pStr = UxFiles.UxFiles.mkStr(ptn);
            try {
                DirectoryInfo dInf = new DirectoryInfo(dStr);
                FileInfo[]    fInf = dInf.GetFiles(pStr);
                int           aLen = fInf.Length;
                if (aLen == 0) {
                    return null;
                } else {
                    int idx;
                    byte** argPtr = (byte**)malloc(sizeof(byte*) * (aLen + 1));
                    for (idx = 0; idx < aLen; idx++) {
                        System.String str = fInf[idx].Name;
                        uint          sHi = (uint) (str.Length + 1);
                        byte* strPtr = (byte*) malloc((int)sHi);
                        UxFiles.UxFiles.MkArr(strPtr, sHi, str);
                        *(argPtr + idx) = strPtr;
                    }
                    *(argPtr + aLen) = null;
                    return (void*) argPtr;
                }
            } catch {
                return null;
            }
        }

// ========================================================================
//   PROCEDURE DisposeArgPtr(aPtr : BuildArgs.ArgPtr);
// ========================================================================
        public static void DisposeArgPtr(void* aPtr) {
            byte** args = (byte**) aPtr;
            if (args != null) {
                byte** next = args;
                while (*next != null) {
                    free((void*) *next);
                    next++;
                }
                free((void*) args);
            }
        }

// ========================================================================

    [DllImport("msvcrt")]
    static extern void* malloc(int siz);

    [DllImport("msvcrt")]
    static extern void free(void* ptr);
    
    } // end class Wildcards
} // end namespace Wildcards
// ========================================================================

namespace SysClock {

    public struct DateTime {
        public uint year;
        public byte month;
        public byte day;
        public byte hour;
        public byte minute;
        public byte second;
        public byte fraction;
        public short zone;
        public byte SymmerTimeFlag;
    } // end DateTime class

    public class SysClock {

        public static byte CanGetClock() {
            return (byte) 1;
        }
  
        public static byte CanSetClock() {
            return (byte) 0;
        }
  
        public static byte IsValidDateTime(DateTime data) {
            throw new System.Exception("IsValidDateTeim not implemented yet");
        }

        private static unsafe void Convert(DateTime* r, System.DateTime s){
            r -> year        = (uint) s.Year;
            r -> month       = (byte) s.Month;
            r -> day         = (byte) s.Day;
            r -> hour        = (byte) s.Hour;
            r -> minute      = (byte) s.Minute;
            r -> second      = (byte) s.Second;
            r -> fraction    = 0;
            r -> zone        = (short) 
                 System.TimeZone.CurrentTimeZone.GetUtcOffset(s).Minutes;
        }

        public static unsafe void GetClock(DateTime* data) {
            System.DateTime now = System.DateTime.Now;
            Convert(data, now);
        }

        public static void SetClock(DateTime data) {
            throw new System.Exception("SetClock not implemented yet");
        }

        public static unsafe void DateTimeFromUnixTime(uint utm, DateTime* res)
        {
             System.DateTime u0time = new System.DateTime(1970,1,1);
             long u0ticks = u0time.Ticks;
             u0ticks += (long)utm * 10000000L;
             Convert(res, new System.DateTime(u0ticks));
        }

    } // end class SysClock
} // end namespace SysClock
// ========================================================================

