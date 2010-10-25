//
//  Runtime system for managed GP Modula-2
//  Copyright (c) QUT, Copyright (c) John Gough 2003
//
//  Notes on overall structure.
//  Programmer accessible code uses normal name mangling, and adds
//  high values for open array parameters.  Methods known to the compiler
//  and accessible at runtime are not nested in any namespace.  Thus the
//  routine that performs big-set union has the CLR name
//  [M2RTS]Helper::cup(int32*, int32*, int32*, unsigned int32)
//
using System;
using System.Reflection;
using System.Runtime.InteropServices;

public unsafe class Helper {

    private static uint bitsInWord = 32;

    private Helper() {
    }  // ensure no instances

    public static string BytePtrToString(byte* ptr, uint len) {
      unchecked { len = len - 1; }
      System.Text.StringBuilder bldr = new System.Text.StringBuilder();
      for (int i = 0; i <= len; i++) {
        char chr = (char)(*(ptr + i));
        if (chr == '\0') break; else bldr.Append(chr);
      }
      return bldr.ToString();
    }

    // ================================================================
    // -------------------- Big bitset operations ---------------------
    // ================================================================

    // Post: *dst is all zeros.
    // *dst is the zero-th word of the bitset.
    //
    public static void clr(int* dst, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            *dst = 0; dst++;
        }
    }


    // Post: *dst is union of *lOp and *rOp
    // *dst is the zero-th word of the bitset.
    //
    public static void cup(int* dst, int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            *dst = *lOp | *rOp; dst++; lOp++; rOp++;
        }
    }


    // Post: *dst is intersection of *lOp and *rOp
    // *dst is the zero-th word of the bitset.
    //
    public static void cap(int* dst, int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            *dst = *lOp & *rOp; dst++; lOp++; rOp++;
        }
    }


    // Post: *dst is exclusive OR of *lOp and *rOp
    // *dst is the zero-th word of the bitset.
    //
    public static void xor(int* dst, int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            *dst = *lOp ^ *rOp; dst++; lOp++; rOp++;
        }
    }


    // Post: *dst is set-difference of *lOp and *rOp
    // *dst is the zero-th word of the bitset.
    //
    public static void dif(int* dst, int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            *dst = *lOp & ~*rOp; dst++; lOp++; rOp++;
        }
    }

    // -------------------- Set range include ---------------------
    //  Insert the bits lo .. hi in the set *dst
    public static void rng(int* dst, uint lo, uint hi) {
       int val;
       uint lRem = lo % bitsInWord; 
       uint lQuo = lo / bitsInWord;
       uint hRem = hi % bitsInWord; 
       uint hQuo = hi / bitsInWord;
       *(dst + lQuo) = -1;
       *(dst + hQuo) = -1;

       // fix first incomplete word
       val = -(1 << (int)lRem);
       *(dst + lQuo) &= val;
       lQuo++;

       // fix last incomplete word
       val = ~(-(2 << (int)hRem));
       *(dst + hQuo) &= val;

       for ( ; lQuo < hQuo; lQuo++) {
           *(dst + lQuo) = -1;
       }
    }

    //
    // ----------------- String length compute -------------------
    //
    public static uint strLen(byte* src, uint hi) {
       uint index;
       for (index = 0; index <= hi; index++) {
          if (*(src + index) == (byte)0) return index;
       }
       return hi;
    }

    //
    // ---------------- Int32 Modulus function ----------------
    //
    public static int modI(int lhs, int rhs) {
       // This version for positive rhs only ...
       // the function is different for Component Pascal.
       int res = lhs % rhs;
       if (res < 0) res += rhs;
       return res;
    }
    
    //
    // ---------------- Int32 Modulus function ----------------
    //
    public static int divI(int lhs, int rhs) {
       // This version for positive rhs only ...
       // the function is different for Component Pascal.
       if (lhs < 0) lhs -= (rhs-1);
       return lhs / rhs;
    }
    
    //
    // ---------------- Int64 Modulus function ----------------
    //
    public static long modH(long lhs, long rhs) {
    // // This version for positive rhs only ...
    // // the function is different for Component Pascal.
    // long res = lhs % rhs;
    // if (res < 0) res += rhs;
    // return res;
       //
       // This version for all four quadrants, same as GPCP
       //
       if (rhs == -1) return 0;

       long rslt = lhs % rhs;
       if ((lhs < 0 != rhs < 0) && (rslt != 0))
           rslt += rhs;
       return rslt;
    }
    
    //
    // ---------------- Int64 Remainder function --------------
    //
    public static long remH(long lhs, long rhs) {
       //
       // This version for all four quadrants, same as GPCP
       //
       if (rhs == -1) return 0;
       else return (lhs % rhs);
    }
    
    //
    // ---------------- Int64 Modulus function ----------------
    //
    public static long divH(long lhs, long rhs) {
    //
    // // This version for positive rhs only ...
    // // the function is different for Component Pascal.
    // if (lhs < 0) lhs -= (rhs-1);
    // return lhs / rhs;
       //
       // This version for all four quadrants, same as GPCP
       //
       long rslt = lhs / rhs;
       long remV = lhs % rhs;
       if ((lhs < 0 != rhs < 0) && (remV != 0))
           rslt--;
       return rslt;
    }
    
    // ================================================================
    // --------------------- Big bitset relops ------------------------
    // ================================================================

    // Post: returns bool indicating (partial) ordering of bitsets
    //
    public static bool setEQ(int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            if (*lOp != *rOp) return false;
            lOp++; rOp++;
        }
        return true;
    }

    public static bool setNE(int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            if (*lOp != *rOp) return true;
            lOp++; rOp++;
        }
        return false;
    }


    public static bool setGE(int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            if ((*lOp | *rOp) != *lOp) return false;
            lOp++; rOp++;
        }
        return true;
    }


    public static bool setLE(int* lOp, int* rOp, uint eNm) {
        for ( ; eNm > 0; eNm--) {
            if ((*lOp & *rOp) != *lOp) return false;
            lOp++; rOp++;
        }
        return true;
    }

}

// ========================================================================
// ========================================================================
// ========================================================================

public unsafe class Traps {

    private Traps() { }

    private static char[] separators = {'%'};


    // -------------- Notes on string mangling helpers -------------------
    //
    //   Incoming strings have form
    //      ".......%.......%......" where '.' is any character and the
    //      separator character '%' is literal.
    //   Result string has numbers interpolated into the separator 
    //   positions.
    //
    //   There are one, two and three separator versions for both signed
    //   and unsigned integer arguments.
    //
    // ------------ End notes on string mangling helpers -----------------

    public static string mangle(int val, string str) {
        string vStr = Convert.ToString(val);
        string[] sArr = str.Split(separators);
        return sArr[0] + vStr + sArr[1];
    }

    public static string mangle(int val, int lo, string str) {
        string vStr = Convert.ToString(val);
        string lStr = Convert.ToString(lo);
        string[] sArr = str.Split(separators);
        return sArr[0] + vStr + sArr[1] + lStr + sArr[2];
    }

    public static string mangle(int val, int lo, int hi, string str) {
        string vStr = Convert.ToString(val);
        string lStr = Convert.ToString(lo);
        string hStr = Convert.ToString(hi);
        string[] sArr = str.Split(separators);
        return sArr[0] + vStr + sArr[1] + lStr + sArr[2] + hStr + sArr[3];
    }


    public static string mangle(uint val, string str) {
        string vStr = Convert.ToString(val);
        string[] sArr = str.Split(separators);
        return sArr[0] + vStr + sArr[1];
    }

    public static string mangle(uint val, uint lo, string str) {
        string vStr = Convert.ToString(val);
        string lStr = Convert.ToString(lo);
        string[] sArr = str.Split(separators);
        return sArr[0] + vStr + sArr[1] + lStr + sArr[2];
    }

    public static string mangle(uint val, uint lo, uint hi, string str) {
        string vStr = Convert.ToString(val);
        string lStr = Convert.ToString(lo);
        string hStr = Convert.ToString(hi);
        string[] sArr = str.Split(separators);
        return sArr[0] + vStr + sArr[1] + lStr + sArr[2] + hStr + sArr[3];
    }

    public static string mangle(byte* str, uint lNm) {
        System.Text.StringBuilder bld = new System.Text.StringBuilder(80);  
        if (lNm != 0) {
            bld.Append("Program assertion failed: ");
            while (*str != (byte) 0) {
                bld.Append((char) *str); str++;
            }
            bld.Append(':');
            bld.Append((int) lNm);
        } else {
            while (*str != (byte) 0) {
                bld.Append((char) *str); str++;
            }
        }
        return bld.ToString();
    }

    public static void EmitExString(Exception ex) {
        System.Console.Error.WriteLine(ex.ToString());
    }

    public static int timeTrap() {
        return time(0);
    }

    // =============================================================
    [DllImport("msvcrt")]
    static extern int time(int dummy);

}
// ========================================================================
// ========================================================================
// ========================================================================

namespace ProgArgs {
    //
    //  ProgArgs provides some program argument handling.
    //  The entry point of every GPM program saves its argments (if any)
    //  to a static field in this namespace.
    //
    //  There are also a number of low-level utilities unrelated to 
    //  program arguments that traditionally live in this module.
    //
    public unsafe class ProgArgs {

        public static byte FP_Overflow;

        private static string[] argv;

        private ProgArgs() {}

        private static System.String mkStr(byte* arr) {
            System.Text.StringBuilder bld = new System.Text.StringBuilder(20);  
            int ix = 0;
            char chr = (char) *(arr+ix); ix++;
            while (chr != '\0') {
                bld.Append(chr);
                chr = (char) *(arr+ix); ix++;
            } 
            return bld.ToString();
        }

        private static void MkArr(byte* dst, uint hiD, string arg) {
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

        public static void __save(string[] args) {
            argv = args;
        }

        public static uint ArgNumber() {
            return (uint)argv.Length;
        }

        public static void GetArg(uint num, byte* arg, uint hiA) {
            string str = argv[num];
            MkArr(arg, hiA, str);
        }

//  ========================================================================
//  PROCEDURE EnvironString(inStr  : ARRAY OF CHAR;
//                      VAR outStr : ARRAY OF CHAR);
//  ========================================================================
        public static void EnvironString(byte* inStr,  uint hiI,
                                         byte* outStr, uint hiO) 
        {
            *(inStr+hiI) = (byte) 0; // ensure string terminated
            string srcS = mkStr(inStr);
            string dstS = System.Environment.GetEnvironmentVariable(srcS);
            MkArr(outStr, hiO, dstS);
        }

//  ========================================================================
//  PROCEDURE VersionTime(VAR outStr  : ARRAY OF CHAR);
//  ========================================================================
        public static void VersionTime(byte* outStr, uint hiA) {
          try {
            Assembly asm = Assembly.GetEntryAssembly();
            DateTime date = System.IO.File.GetCreationTimeUtc(asm.Location);
            MkArr(outStr, hiA, date.ToString() + '\n');
          }
          catch {
            MkArr(outStr, hiA, "<no version time>\n");
          }
        }

//  ========================================================================
//  PROCEDURE GetMillis() : CARDINAL;
//  ========================================================================
        public static uint GetMillis() {
            return ((uint)(System.DateTime.Now.Ticks / 10000));
        }

    }
}

// ========================================================================
// ========================================================================
// ========================================================================

namespace Vector {

    public unsafe struct Vec {
    //
    //  Support for the vector implementation of "STRING OF T" in GPM.
    //
    //  Vectors have capacity (elNm), and a high tide mark (high).
    //  Element [high] is the last appended element.
    //  Vectors are extended by amortized doubleing, in the case that
    //  new elements are added one at a time.
    //  However, there is support for concatenating either another
    //  vector, or an array of known length.
    //
        public int   elSz;
        public int   elNm;
        public int   high;
        public byte* blob;
    }

    public unsafe class Vector {
       
        private Vector() { }

        public static Vec* newVector(int elemSiz, int elemNum) {
            Vec* ptr = (Vec*) malloc(sizeof(Vec));
            ptr->elSz = elemSiz;
            ptr->elNm = (elemNum + 3) & (-4);
            ptr->blob = (byte*) malloc(elemSiz * ptr->elNm);
            ptr->high = -1;
            return (ptr);
        }

        public static void Dispose(Vec* ptr) {
            free((void*) ptr->blob);
            free((void*) ptr);
        }

        public static void Expand(Vec* ptr, int elemNum) {
            byte* oldBlob = ptr->blob;
            int newSz;
            int oldSz = (ptr->elNm * ptr->elSz);
            int minSz = (elemNum * ptr->elSz);
            if (oldSz * 2 > (minSz + oldSz)) // MAX function
                newSz = oldSz * 2;
            else
                newSz = (minSz + oldSz) & (-4);
    
            byte* newBlob = (byte*) malloc(newSz);
    
            for (int i = 0; i < oldSz; i++) {
                *(newBlob+i) = *(oldBlob+i);
            } 

            free((void*) oldBlob);
            ptr->blob = newBlob;
            ptr->elNm = newSz / ptr->elSz;
        }
    
        //
        //  Trim a m2-char vector so that 'high' is the last non-nul character
        //
        private static void Trim(Vec* ptr) {
            // Assert: this vector is of m2-char
            for (int idx = 0; idx <= ptr->high; idx++) {
                byte chr = *(ptr->blob + idx);
                if (chr == (byte) 0) {
                    ptr->high = idx; return;
                }
            }
        }

        //
        //  Return length of an m2-char vector
        //
        private static int Len(Vec* ptr) {
            // Assert: this vector is of m2-char
            for (int idx = 0; idx <= ptr->high; idx++) {
                if (*(ptr->blob + idx) == (byte) 0) {
                    return idx;
                }
            }
            return ptr->high;
        }

        //
        //  Append m2-chars up to but not including the first nul character.
        //
        private static void ByteAppend(Vec* ptr, byte* src2, int maxL) {
            int idx;
            int jdx = ptr->high;
            for (idx = 0; idx < maxL; idx++) {
                byte chr = *(src2 + idx);
                if (chr == (byte) 0) {
                    ptr->high = jdx; return;
                }
                jdx++; 
                *(ptr->blob + jdx) = chr;
                ptr->high = jdx;
            }
        }
    
        //
        // Need string concatenations also ...
        //    VecConcat, StrConcat, ChrConcat
        //
        public static void CatVec(Vec* vec1, Vec* vec2) {
            Trim(vec1);
            int dlta = Len(vec2);
            if (vec1->high + dlta >= vec1->elNm) {
                Expand(vec1, vec1->high + dlta + 1);
            }
            ByteAppend(vec1, vec2->blob, dlta);
        }
    
        public static void CatArr(Vec* ptr, byte* str, uint sHi) {
            int iHi = (int)sHi;
            Trim(ptr);
            if (ptr->high + iHi >= ptr->elNm) {
                Expand(ptr, ptr->high + iHi + 1);
            }
            ByteAppend(ptr, str, iHi);
        }
    
        public static void CatChr(Vec* ptr, byte chr) {
            Trim(ptr);
            if (chr != (byte) 0) { // append of chr
                ptr->high++;
                if (ptr->high >= ptr->elNm) { 
                   Expand(ptr, ptr->elNm+1); 
                }
                *(ptr->blob + ptr->high) = chr; 
            }
        }
    
    [DllImport("msvcrt")]
    static extern void* malloc(int siz);

    [DllImport("msvcrt")]
    static extern void free(void* ptr);
    
    }
}

// ========================================================================

namespace PcProcesses {

    public unsafe class PcProcesses {

    private const int P_WAIT = 0;

    private PcProcesses() {}

    // ================================================================
    //  PROCEDURE Spawns(comPath : ARRAY OF CHAR;
    //                   argStrg : ARRAY OF CHAR) : SHORTINT; 
    //  (* Spawns another process, and waits for return result *)
    //  (* comPath is an absolute pathname, with extension.    *)
    //  (* argStrn is the additional arguments of the command  *)
    //  (* Arg-0 of command is comPath, others from argStrn.   *)
    //  (* Result is exit code of the spawned process		 *)
    // ================================================================
    public static short Spawns(byte* comPath, uint cHi, 
                               byte* argStrg, uint aHi) {
        uint idx;
        int  state;
        *(comPath+cHi) = (byte) 0; // ensure string terminated
        *(argStrg+aHi) = (byte) 0; // ensure string terminated

        // argStrg is allocated by the caller, so its lifetime is at
        // at least as long as the lifetime of the spawnvp call ...
        byte* [] argBlk = new byte*[256];
        uint aIx = 0;
        argBlk[aIx] = comPath; aIx++;
        //
        //     State Machine ... three states
        // ---------------------------------------
        //  ord state   chr   next     kind
        // ---------------------------------------
        //   0  start  space  start start-state
        //   0  start  nul    end   start-state
        //   0  start  other  cmnd  start-state
        //   1  cmnd   space  start  
        //   1  cmnd   nul    end  
        //   1  cmnd   other  cmnd  
        //   2  end                 no-transitions
        // ---------------------------------------
        //
        state = 0;
        for (idx = 0; idx <= aHi; idx++) {
            byte chr = *(argStrg+idx);
            if (chr == (byte) 0) {
                argBlk[aIx] = null; break;
            } else if (chr == (byte) ' ' || chr == (byte) '\t') {
                state = 0;
                *(argStrg+idx) = (byte) 0; 
            } else if (state == 0) {
                state = 1;
                argBlk[aIx] = (argStrg+idx); aIx++; 
            }
        }
        // must pin the array for this call ...
        fixed (byte** aPtr = &argBlk[0]) 
                           return (short) _spawnvp(P_WAIT, comPath, aPtr);
    }

    // ================================================================
    //  PROCEDURE Spawnv(comPath : ARRAY OF CHAR;
    //                   argvBlk : BuildArgs.ArgPtr) : SHORTINT; 
    //  (* Spawns another process, and waits for return result *)
    //  (* Result is exit code of the spawned process		 *)
    // ================================================================
    public static short Spawnv(byte* comPath, uint high, void* argvBlk) {
        *(comPath+high) = (byte) 0; // ensure string terminated
        return (short) _spawnvp(P_WAIT, comPath, (byte**)argvBlk);
    }

    // ================================================================
    //  PROCEDURE System(command : ARRAY OF CHAR) : SHORTINT; 
    //  (* Spawns another copy of the command processor as     *)
    //  (* specified by the environment variable COMSPEC, this *)
    //  (* executes the command. Returns non-zero on failure   *)
    // ================================================================
    public static ushort System(byte* comPath, uint high) {
        *(comPath+high) = (byte) 0; // ensure string terminated
        return (ushort) _system(comPath);
    }

    // ================================================================
    //  PROCEDURE PSP() : ADDRESS;   -- the process "pid"
    // ================================================================
    public static void* PSP() {
        return _getpid();
    }

    // ================================================================
    [DllImport("msvcrt")]
    static extern void* _getpid();

    [DllImport("msvcrt")]
    static extern int _spawnvp(int wait, byte* str, byte** args);

    [DllImport("msvcrt")]
    static extern int _system(byte* str);


    } // end class PcProcesses
} // end namespace PcProcesses
// ========================================================================
// ========================================================================
// ========================================================================
// ========================================================================
