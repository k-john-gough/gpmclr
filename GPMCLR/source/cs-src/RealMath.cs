//  
//  Wrapper functions to implement modula-2 math library functions.
//  kjg October 2003;
//
using System;

namespace RealMath {
public class RealMath {

//
//CONST
//  pi   = 3.1415926535897932384626433832795028841972;
//  exp1 = 2.7182818284590452353602874713526624977572;
//
//PROCEDURE sqrt (x: REAL): REAL;
//  (* Returns the positive square root of x *)
//
    public static double sqrt(double x) {
        return Math.Sqrt(x);
    }
//
//PROCEDURE exp (x: REAL): REAL;
//  (* Returns the exponential of x *)
//
    public static double exp(double x) {
        return Math.Exp(x);
    }
//
//PROCEDURE ln (x: REAL): REAL;
//  (* Returns the natural logarithm of x *)
//
    public static double ln(double x) {
        return Math.Log(x);
    }
//
//  (* The angle in all trigonometric functions is measured in radians *)
//
//PROCEDURE sin (x: REAL): REAL;
//  (* Returns the sine of x *)
//
    public static double sin(double x) {
        return Math.Sin(x);
    }
//
//PROCEDURE cos (x: REAL): REAL;
//  (* Returns the cosine of x *)
//
    public static double cos(double x) {
        return Math.Cos(x);
    }
//
//PROCEDURE tan (x: REAL): REAL;
//  (* Returns the tangent of x *)
//
    public static double tan(double x) {
        return Math.Tan(x);
    }
//
//PROCEDURE arcsin (x: REAL): REAL;
//  (* Returns the arcsine of x *)
//
    public static double arcsin(double x) {
        return Math.Asin(x);
    }
//
//PROCEDURE arccos (x: REAL): REAL;
//  (* Returns the arccosine of x *)
//
    public static double arccos(double x) {
        return Math.Acos(x);
    }
//
//PROCEDURE arctan (x: REAL): REAL;
//  (* Returns the arctangent of x *)
//
    public static double arctan(double x) {
        return Math.Atan(x);
    }
//
//PROCEDURE power (base, exponent: REAL): REAL;
//  (* Returns the value of the number base raised to the power exponent *)
//
    public static double power(double b, double e) {
        return Math.Pow(b, e);
    }
//
//PROCEDURE round (x: REAL): INTEGER;
//  (* Returns the value of x rounded to the nearest integer *)
//
    public static int round(double x) {
        return (int) Math.Round(x);  // should be trapping!
    }
//
//PROCEDURE IsRMathException (): BOOLEAN;
//  (* Returns TRUE if the current coroutine is in the exceptional execution
//     state because of the raising of an exception in a routine from this 
//     module; otherwise returns FALSE.
//  *)
//
//END RealMath.
    }
}
