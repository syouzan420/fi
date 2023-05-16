"use strict";
var __haste_prog_id = '32524608d5cf7cd347b08e4859e63ed54fa745738a2c40d7139f6fed30a6cc21';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=__Z,_1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2=function(_){return new F(function(){return __jsNull();});},_3=function(_4){var _5=B(A1(_4,_));return E(_5);},_6=new T(function(){return B(_3(_2));}),_7=new T(function(){return E(_6);}),_8="metaKey",_9="shiftKey",_a="altKey",_b="ctrlKey",_c="keyCode",_d=function(_e,_){var _f=__get(_e,E(_c)),_g=__get(_e,E(_b)),_h=__get(_e,E(_a)),_i=__get(_e,E(_9)),_j=__get(_e,E(_8));return new T(function(){var _k=Number(_f),_l=jsTrunc(_k);return new T5(0,_l,E(_g),E(_h),E(_i),E(_j));});},_m=function(_n,_o,_){return new F(function(){return _d(E(_o),_);});},_p="keydown",_q="keyup",_r="keypress",_s=function(_t){switch(E(_t)){case 0:return E(_r);case 1:return E(_q);default:return E(_p);}},_u=new T2(0,_s,_m),_v="deltaZ",_w="deltaY",_x="deltaX",_y=function(_z,_A){var _B=E(_z);return (_B._==0)?E(_A):new T2(1,_B.a,new T(function(){return B(_y(_B.b,_A));}));},_C=function(_D,_E){var _F=jsShowI(_D);return new F(function(){return _y(fromJSStr(_F),_E);});},_G=41,_H=40,_I=function(_J,_K,_L){if(_K>=0){return new F(function(){return _C(_K,_L);});}else{if(_J<=6){return new F(function(){return _C(_K,_L);});}else{return new T2(1,_H,new T(function(){var _M=jsShowI(_K);return B(_y(fromJSStr(_M),new T2(1,_G,_L)));}));}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_I(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_I(0,_R,_P));}))));});},_S=function(_T,_){return new T(function(){var _U=Number(E(_T)),_V=jsTrunc(_U);if(_V<0){return B(_Q(_V));}else{if(_V>2){return B(_Q(_V));}else{return _V;}}});},_W=0,_X=new T3(0,_W,_W,_W),_Y="button",_Z=new T(function(){return eval("jsGetMouseCoords");}),_10=__Z,_11=function(_12,_){var _13=E(_12);if(!_13._){return _10;}else{var _14=B(_11(_13.b,_));return new T2(1,new T(function(){var _15=Number(E(_13.a));return jsTrunc(_15);}),_14);}},_16=function(_17,_){var _18=__arr2lst(0,_17);return new F(function(){return _11(_18,_);});},_19=function(_1a,_){return new F(function(){return _16(E(_1a),_);});},_1b=function(_1c,_){return new T(function(){var _1d=Number(E(_1c));return jsTrunc(_1d);});},_1e=new T2(0,_1b,_19),_1f=function(_1g,_){var _1h=E(_1g);if(!_1h._){return _10;}else{var _1i=B(_1f(_1h.b,_));return new T2(1,_1h.a,_1i);}},_1j=new T(function(){return B(unCStr("base"));}),_1k=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1l=new T(function(){return B(unCStr("IOException"));}),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1j,_1k,_1l),_1n=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1m,_10,_10),_1o=function(_1p){return E(_1n);},_1q=function(_1r){return E(E(_1r).a);},_1s=function(_1t,_1u,_1v){var _1w=B(A1(_1t,_)),_1x=B(A1(_1u,_)),_1y=hs_eqWord64(_1w.a,_1x.a);if(!_1y){return __Z;}else{var _1z=hs_eqWord64(_1w.b,_1x.b);return (!_1z)?__Z:new T1(1,_1v);}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1s(B(_1q(_1C.a)),_1o,_1C.b);});},_1D=new T(function(){return B(unCStr(": "));}),_1E=new T(function(){return B(unCStr(")"));}),_1F=new T(function(){return B(unCStr(" ("));}),_1G=new T(function(){return B(unCStr("interrupted"));}),_1H=new T(function(){return B(unCStr("system error"));}),_1I=new T(function(){return B(unCStr("unsatisified constraints"));}),_1J=new T(function(){return B(unCStr("user error"));}),_1K=new T(function(){return B(unCStr("permission denied"));}),_1L=new T(function(){return B(unCStr("illegal operation"));}),_1M=new T(function(){return B(unCStr("end of file"));}),_1N=new T(function(){return B(unCStr("resource exhausted"));}),_1O=new T(function(){return B(unCStr("resource busy"));}),_1P=new T(function(){return B(unCStr("does not exist"));}),_1Q=new T(function(){return B(unCStr("already exists"));}),_1R=new T(function(){return B(unCStr("resource vanished"));}),_1S=new T(function(){return B(unCStr("timeout"));}),_1T=new T(function(){return B(unCStr("unsupported operation"));}),_1U=new T(function(){return B(unCStr("hardware fault"));}),_1V=new T(function(){return B(unCStr("inappropriate type"));}),_1W=new T(function(){return B(unCStr("invalid argument"));}),_1X=new T(function(){return B(unCStr("failed"));}),_1Y=new T(function(){return B(unCStr("protocol error"));}),_1Z=function(_20,_21){switch(E(_20)){case 0:return new F(function(){return _y(_1Q,_21);});break;case 1:return new F(function(){return _y(_1P,_21);});break;case 2:return new F(function(){return _y(_1O,_21);});break;case 3:return new F(function(){return _y(_1N,_21);});break;case 4:return new F(function(){return _y(_1M,_21);});break;case 5:return new F(function(){return _y(_1L,_21);});break;case 6:return new F(function(){return _y(_1K,_21);});break;case 7:return new F(function(){return _y(_1J,_21);});break;case 8:return new F(function(){return _y(_1I,_21);});break;case 9:return new F(function(){return _y(_1H,_21);});break;case 10:return new F(function(){return _y(_1Y,_21);});break;case 11:return new F(function(){return _y(_1X,_21);});break;case 12:return new F(function(){return _y(_1W,_21);});break;case 13:return new F(function(){return _y(_1V,_21);});break;case 14:return new F(function(){return _y(_1U,_21);});break;case 15:return new F(function(){return _y(_1T,_21);});break;case 16:return new F(function(){return _y(_1S,_21);});break;case 17:return new F(function(){return _y(_1R,_21);});break;default:return new F(function(){return _y(_1G,_21);});}},_22=new T(function(){return B(unCStr("}"));}),_23=new T(function(){return B(unCStr("{handle: "));}),_24=function(_25,_26,_27,_28,_29,_2a){var _2b=new T(function(){var _2c=new T(function(){var _2d=new T(function(){var _2e=E(_28);if(!_2e._){return E(_2a);}else{var _2f=new T(function(){return B(_y(_2e,new T(function(){return B(_y(_1E,_2a));},1)));},1);return B(_y(_1F,_2f));}},1);return B(_1Z(_26,_2d));}),_2g=E(_27);if(!_2g._){return E(_2c);}else{return B(_y(_2g,new T(function(){return B(_y(_1D,_2c));},1)));}}),_2h=E(_29);if(!_2h._){var _2i=E(_25);if(!_2i._){return E(_2b);}else{var _2j=E(_2i.a);if(!_2j._){var _2k=new T(function(){var _2l=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2l));},1);return new F(function(){return _y(_23,_2k);});}else{var _2m=new T(function(){var _2n=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2n));},1);return new F(function(){return _y(_23,_2m);});}}}else{return new F(function(){return _y(_2h.a,new T(function(){return B(_y(_1D,_2b));},1));});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _24(_2q.a,_2q.b,_2q.c,_2q.d,_2q.f,_10);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _24(_2v.a,_2v.b,_2v.c,_2v.d,_2v.f,_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _24(_2z.a,_2z.b,_2z.c,_2z.d,_2z.f,_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H._){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=new T(function(){var _2J=new T(function(){var _2K=function(_2L){var _2M=E(_2L);if(!_2M._){return E(new T2(1,_2B,_2G));}else{var _2N=new T(function(){return B(A2(_2E,_2M.a,new T(function(){return B(_2K(_2M.b));})));});return new T2(1,_2A,_2N);}};return B(_2K(_2H.b));});return B(A2(_2E,_2H.a,_2J));});return new T2(1,_2C,_2I);}},_2O=function(_2P,_2Q){return new F(function(){return _2D(_2w,_2P,_2Q);});},_2R=new T3(0,_2r,_2o,_2O),_2S=new T(function(){return new T5(0,_1o,_2R,_2T,_1A,_2o);}),_2T=function(_2U){return new T2(0,_2S,_2U);},_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_0,_2V,_10,_2W,_0,_0),_2Y=new T(function(){return B(_2T(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1f(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_3d,_3e,_){if(E(_3d)==7){var _3f=__app1(E(_Z),_3e),_3g=B(_32(_1e,_1e,_3f,_)),_3h=__get(_3e,E(_x)),_3i=__get(_3e,E(_w)),_3j=__get(_3e,E(_v));return new T(function(){return new T3(0,E(_3g),E(_0),E(new T3(0,_3h,_3i,_3j)));});}else{var _3k=__app1(E(_Z),_3e),_3l=B(_32(_1e,_1e,_3k,_)),_3m=__get(_3e,E(_Y)),_3n=__eq(_3m,E(_7));if(!E(_3n)){var _3o=__isUndef(_3m);if(!E(_3o)){var _3p=B(_S(_3m,_));return new T(function(){return new T3(0,E(_3l),E(new T1(1,_3p)),E(_X));});}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}},_3q=function(_3r,_3s,_){return new F(function(){return _3c(_3r,E(_3s),_);});},_3t="mouseout",_3u="mouseover",_3v="mousemove",_3w="mouseup",_3x="mousedown",_3y="dblclick",_3z="click",_3A="wheel",_3B=function(_3C){switch(E(_3C)){case 0:return E(_3z);case 1:return E(_3y);case 2:return E(_3x);case 3:return E(_3w);case 4:return E(_3v);case 5:return E(_3u);case 6:return E(_3t);default:return E(_3A);}},_3D=new T2(0,_3B,_3q),_3E=function(_3F){return E(_3F);},_3G=function(_3H,_3I){return E(_3H)==E(_3I);},_3J=function(_3K,_3L){return E(_3K)!=E(_3L);},_3M=new T2(0,_3G,_3J),_3N="screenY",_3O="screenX",_3P="clientY",_3Q="clientX",_3R="pageY",_3S="pageX",_3T="target",_3U="identifier",_3V=function(_3W,_){var _3X=__get(_3W,E(_3U)),_3Y=__get(_3W,E(_3T)),_3Z=__get(_3W,E(_3S)),_40=__get(_3W,E(_3R)),_41=__get(_3W,E(_3Q)),_42=__get(_3W,E(_3P)),_43=__get(_3W,E(_3O)),_44=__get(_3W,E(_3N));return new T(function(){var _45=Number(_3X),_46=jsTrunc(_45);return new T5(0,_46,_3Y,E(new T2(0,new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}),new T(function(){var _48=Number(_40);return jsTrunc(_48);}))),E(new T2(0,new T(function(){var _49=Number(_41);return jsTrunc(_49);}),new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}))),E(new T2(0,new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}),new T(function(){var _4c=Number(_44);return jsTrunc(_4c);}))));});},_4d=function(_4e,_){var _4f=E(_4e);if(!_4f._){return _10;}else{var _4g=B(_3V(E(_4f.a),_)),_4h=B(_4d(_4f.b,_));return new T2(1,_4g,_4h);}},_4i="touches",_4j=function(_4k){return E(E(_4k).b);},_4l=function(_4m,_4n,_){var _4o=__arr2lst(0,_4n),_4p=new T(function(){return B(_4j(_4m));}),_4q=function(_4r,_){var _4s=E(_4r);if(!_4s._){return _10;}else{var _4t=B(A2(_4p,_4s.a,_)),_4u=B(_4q(_4s.b,_));return new T2(1,_4t,_4u);}};return new F(function(){return _4q(_4o,_);});},_4v=function(_4w,_){return new F(function(){return _4l(_1e,E(_4w),_);});},_4x=new T2(0,_19,_4v),_4y=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4z=function(_4A){return E(E(_4A).a);},_4B=function(_4C,_4D,_4E){while(1){var _4F=E(_4E);if(!_4F._){return false;}else{if(!B(A3(_4z,_4C,_4D,_4F.a))){_4E=_4F.b;continue;}else{return true;}}}},_4G=function(_4H,_4I){while(1){var _4J=B((function(_4K,_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{var _4N=_4M.a,_4O=_4M.b;if(!B(A1(_4K,_4N))){var _4P=_4K;_4H=_4P;_4I=_4O;return __continue;}else{return new T2(1,_4N,new T(function(){return B(_4G(_4K,_4O));}));}}})(_4H,_4I));if(_4J!=__continue){return _4J;}}},_4Q=function(_4R,_){var _4S=__get(_4R,E(_4i)),_4T=__arr2lst(0,_4S),_4U=B(_4d(_4T,_)),_4V=__app1(E(_4y),_4R),_4W=B(_32(_4x,_4x,_4V,_)),_4X=E(_4W),_4Y=new T(function(){var _4Z=function(_50){return new F(function(){return _4B(_3M,new T(function(){return E(_50).a;}),_4X.a);});};return B(_4G(_4Z,_4U));}),_51=new T(function(){var _52=function(_53){return new F(function(){return _4B(_3M,new T(function(){return E(_53).a;}),_4X.b);});};return B(_4G(_52,_4U));});return new T3(0,_4U,_51,_4Y);},_54=function(_55,_56,_){return new F(function(){return _4Q(E(_56),_);});},_57="touchcancel",_58="touchend",_59="touchmove",_5a="touchstart",_5b=function(_5c){switch(E(_5c)){case 0:return E(_5a);case 1:return E(_59);case 2:return E(_58);default:return E(_57);}},_5d=new T2(0,_5b,_54),_5e=function(_5f,_5g,_){var _5h=B(A1(_5f,_)),_5i=B(A1(_5g,_));return _5h;},_5j=function(_5k,_5l,_){var _5m=B(A1(_5k,_)),_5n=B(A1(_5l,_));return new T(function(){return B(A1(_5m,_5n));});},_5o=function(_5p,_5q,_){var _5r=B(A1(_5q,_));return _5p;},_5s=function(_5t,_5u,_){var _5v=B(A1(_5u,_));return new T(function(){return B(A1(_5t,_5v));});},_5w=new T2(0,_5s,_5o),_5x=function(_5y,_){return _5y;},_5z=function(_5A,_5B,_){var _5C=B(A1(_5A,_));return new F(function(){return A1(_5B,_);});},_5D=new T5(0,_5w,_5x,_5j,_5z,_5e),_5E=new T(function(){return E(_2S);}),_5F=function(_5G){return E(E(_5G).c);},_5H=function(_5I){return new T6(0,_0,_2V,_10,_5I,_0,_0);},_5J=function(_5K,_){var _5L=new T(function(){return B(A2(_5F,_5E,new T(function(){return B(A1(_5H,_5K));})));});return new F(function(){return die(_5L);});},_5M=function(_5N,_){return new F(function(){return _5J(_5N,_);});},_5O=function(_5P){return new F(function(){return A1(_5M,_5P);});},_5Q=function(_5R,_5S,_){var _5T=B(A1(_5R,_));return new F(function(){return A2(_5S,_5T,_);});},_5U=new T5(0,_5D,_5Q,_5z,_5x,_5O),_5V=function(_5W){return E(_5W);},_5X=new T2(0,_5U,_5V),_5Y=new T2(0,_5X,_5x),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_60=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_61=new T(function(){return eval("(function(cv){return cv.height})");}),_62=new T(function(){return eval("(function(cv){return cv.width})");}),_63=function(_64,_){var _65=__app1(E(_62),_64),_66=__app1(E(_61),_64),_67=__app1(E(_60),_64),_68=__app1(E(_5Z),_64);return new T2(0,new T(function(){return _65/_67;}),new T(function(){return _66/_68;}));},_69=function(_6a,_6b){return E(_6a)!=E(_6b);},_6c=function(_6d,_6e){return E(_6d)==E(_6e);},_6f=new T2(0,_6c,_69),_6g=function(_6h,_6i){switch(E(_6h)){case 0:return (E(_6i)==0)?true:false;case 1:return (E(_6i)==1)?true:false;case 2:return (E(_6i)==2)?true:false;case 3:return (E(_6i)==3)?true:false;case 4:return (E(_6i)==4)?true:false;case 5:return (E(_6i)==5)?true:false;case 6:return (E(_6i)==6)?true:false;case 7:return (E(_6i)==7)?true:false;default:return (E(_6i)==8)?true:false;}},_6j=function(_6k,_6l,_6m,_6n){if(_6k!=_6m){return false;}else{return new F(function(){return _6g(_6l,_6n);});}},_6o=function(_6p,_6q){var _6r=E(_6p),_6s=E(_6q);return new F(function(){return _6j(E(_6r.a),_6r.b,E(_6s.a),_6s.b);});},_6t=function(_6u,_6v,_6w,_6x){if(_6u!=_6w){return true;}else{switch(E(_6v)){case 0:return (E(_6x)==0)?false:true;case 1:return (E(_6x)==1)?false:true;case 2:return (E(_6x)==2)?false:true;case 3:return (E(_6x)==3)?false:true;case 4:return (E(_6x)==4)?false:true;case 5:return (E(_6x)==5)?false:true;case 6:return (E(_6x)==6)?false:true;case 7:return (E(_6x)==7)?false:true;default:return (E(_6x)==8)?false:true;}}},_6y=function(_6z,_6A){var _6B=E(_6z),_6C=E(_6A);return new F(function(){return _6t(E(_6B.a),_6B.b,E(_6C.a),_6C.b);});},_6D=new T2(0,_6o,_6y),_6E=function(_6F,_6G,_6H){while(1){var _6I=E(_6G);if(!_6I._){return (E(_6H)._==0)?true:false;}else{var _6J=E(_6H);if(!_6J._){return false;}else{if(!B(A3(_4z,_6F,_6I.a,_6J.a))){return false;}else{_6G=_6I.b;_6H=_6J.b;continue;}}}}},_6K=function(_6L,_6M){return (!B(_6E(_6D,_6L,_6M)))?true:false;},_6N=function(_6O,_6P){return new F(function(){return _6E(_6D,_6O,_6P);});},_6Q=new T2(0,_6N,_6K),_6R=function(_6S,_6T,_6U){return new F(function(){return A1(_6S,new T2(1,_2A,new T(function(){return B(A1(_6T,_6U));})));});},_6V=new T(function(){return B(unCStr("!!: negative index"));}),_6W=new T(function(){return B(unCStr("Prelude."));}),_6X=new T(function(){return B(_y(_6W,_6V));}),_6Y=new T(function(){return B(err(_6X));}),_6Z=new T(function(){return B(unCStr("!!: index too large"));}),_70=new T(function(){return B(_y(_6W,_6Z));}),_71=new T(function(){return B(err(_70));}),_72=function(_73,_74){while(1){var _75=E(_73);if(!_75._){return E(_71);}else{var _76=E(_74);if(!_76){return E(_75.a);}else{_73=_75.b;_74=_76-1|0;continue;}}}},_77=function(_78,_79){if(_79>=0){return new F(function(){return _72(_78,_79);});}else{return E(_6Y);}},_7a=function(_7b,_7c){while(1){var _7d=E(_7b);if(!_7d._){return E(_7c);}else{var _7e=_7c+1|0;_7b=_7d.b;_7c=_7e;continue;}}},_7f=0,_7g=function(_){return _7f;},_7h=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_7i=function(_7j,_7k,_7l){var _7m=new T(function(){return toJSStr(E(_7l));});return function(_7n,_){var _7o=__app4(E(_7h),E(_7n),E(_7m),E(_7j),E(_7k));return new F(function(){return _7g(_);});};},_7p=new T1(0,1),_7q=function(_7r,_7s){var _7t=E(_7r);if(!_7t._){var _7u=_7t.a,_7v=E(_7s);if(!_7v._){var _7w=_7v.a;return (_7u!=_7w)?(_7u>_7w)?2:0:1;}else{var _7x=I_compareInt(_7v.a,_7u);return (_7x<=0)?(_7x>=0)?1:2:0;}}else{var _7y=_7t.a,_7z=E(_7s);if(!_7z._){var _7A=I_compareInt(_7y,_7z.a);return (_7A>=0)?(_7A<=0)?1:2:0;}else{var _7B=I_compare(_7y,_7z.a);return (_7B>=0)?(_7B<=0)?1:2:0;}}},_7C=new T(function(){return B(unCStr("base"));}),_7D=new T(function(){return B(unCStr("GHC.Exception"));}),_7E=new T(function(){return B(unCStr("ArithException"));}),_7F=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7C,_7D,_7E),_7G=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7F,_10,_10),_7H=function(_7I){return E(_7G);},_7J=function(_7K){var _7L=E(_7K);return new F(function(){return _1s(B(_1q(_7L.a)),_7H,_7L.b);});},_7M=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_7N=new T(function(){return B(unCStr("denormal"));}),_7O=new T(function(){return B(unCStr("divide by zero"));}),_7P=new T(function(){return B(unCStr("loss of precision"));}),_7Q=new T(function(){return B(unCStr("arithmetic underflow"));}),_7R=new T(function(){return B(unCStr("arithmetic overflow"));}),_7S=function(_7T,_7U){switch(E(_7T)){case 0:return new F(function(){return _y(_7R,_7U);});break;case 1:return new F(function(){return _y(_7Q,_7U);});break;case 2:return new F(function(){return _y(_7P,_7U);});break;case 3:return new F(function(){return _y(_7O,_7U);});break;case 4:return new F(function(){return _y(_7N,_7U);});break;default:return new F(function(){return _y(_7M,_7U);});}},_7V=function(_7W){return new F(function(){return _7S(_7W,_10);});},_7X=function(_7Y,_7Z,_80){return new F(function(){return _7S(_7Z,_80);});},_81=function(_82,_83){return new F(function(){return _2D(_7S,_82,_83);});},_84=new T3(0,_7X,_7V,_81),_85=new T(function(){return new T5(0,_7H,_84,_86,_7J,_7V);}),_86=function(_87){return new T2(0,_85,_87);},_88=3,_89=new T(function(){return B(_86(_88));}),_8a=new T(function(){return die(_89);}),_8b=function(_8c,_8d){var _8e=E(_8c);return (_8e._==0)?_8e.a*Math.pow(2,_8d):I_toNumber(_8e.a)*Math.pow(2,_8d);},_8f=function(_8g,_8h){var _8i=E(_8g);if(!_8i._){var _8j=_8i.a,_8k=E(_8h);return (_8k._==0)?_8j==_8k.a:(I_compareInt(_8k.a,_8j)==0)?true:false;}else{var _8l=_8i.a,_8m=E(_8h);return (_8m._==0)?(I_compareInt(_8l,_8m.a)==0)?true:false:(I_compare(_8l,_8m.a)==0)?true:false;}},_8n=function(_8o){var _8p=E(_8o);if(!_8p._){return E(_8p.a);}else{return new F(function(){return I_toInt(_8p.a);});}},_8q=function(_8r,_8s){while(1){var _8t=E(_8r);if(!_8t._){var _8u=_8t.a,_8v=E(_8s);if(!_8v._){var _8w=_8v.a,_8x=addC(_8u,_8w);if(!E(_8x.b)){return new T1(0,_8x.a);}else{_8r=new T1(1,I_fromInt(_8u));_8s=new T1(1,I_fromInt(_8w));continue;}}else{_8r=new T1(1,I_fromInt(_8u));_8s=_8v;continue;}}else{var _8y=E(_8s);if(!_8y._){_8r=_8t;_8s=new T1(1,I_fromInt(_8y.a));continue;}else{return new T1(1,I_add(_8t.a,_8y.a));}}}},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C._){var _8D=E(_8C.a);if(_8D==( -2147483648)){_8A=new T1(1,I_fromInt( -2147483648));continue;}else{var _8E=E(_8B);if(!_8E._){var _8F=_8E.a;return new T2(0,new T1(0,quot(_8D,_8F)),new T1(0,_8D%_8F));}else{_8A=new T1(1,I_fromInt(_8D));_8B=_8E;continue;}}}else{var _8G=E(_8B);if(!_8G._){_8A=_8C;_8B=new T1(1,I_fromInt(_8G.a));continue;}else{var _8H=I_quotRem(_8C.a,_8G.a);return new T2(0,new T1(1,_8H.a),new T1(1,_8H.b));}}}},_8I=new T1(0,0),_8J=function(_8K,_8L){while(1){var _8M=E(_8K);if(!_8M._){_8K=new T1(1,I_fromInt(_8M.a));continue;}else{return new T1(1,I_shiftLeft(_8M.a,_8L));}}},_8N=function(_8O,_8P,_8Q){if(!B(_8f(_8Q,_8I))){var _8R=B(_8z(_8P,_8Q)),_8S=_8R.a;switch(B(_7q(B(_8J(_8R.b,1)),_8Q))){case 0:return new F(function(){return _8b(_8S,_8O);});break;case 1:if(!(B(_8n(_8S))&1)){return new F(function(){return _8b(_8S,_8O);});}else{return new F(function(){return _8b(B(_8q(_8S,_7p)),_8O);});}break;default:return new F(function(){return _8b(B(_8q(_8S,_7p)),_8O);});}}else{return E(_8a);}},_8T=function(_8U,_8V){var _8W=E(_8U);if(!_8W._){var _8X=_8W.a,_8Y=E(_8V);return (_8Y._==0)?_8X>_8Y.a:I_compareInt(_8Y.a,_8X)<0;}else{var _8Z=_8W.a,_90=E(_8V);return (_90._==0)?I_compareInt(_8Z,_90.a)>0:I_compare(_8Z,_90.a)>0;}},_91=new T1(0,1),_92=function(_93,_94){var _95=E(_93);if(!_95._){var _96=_95.a,_97=E(_94);return (_97._==0)?_96<_97.a:I_compareInt(_97.a,_96)>0;}else{var _98=_95.a,_99=E(_94);return (_99._==0)?I_compareInt(_98,_99.a)<0:I_compare(_98,_99.a)<0;}},_9a=new T(function(){return B(unCStr("base"));}),_9b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_9c=new T(function(){return B(unCStr("PatternMatchFail"));}),_9d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9a,_9b,_9c),_9e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9d,_10,_10),_9f=function(_9g){return E(_9e);},_9h=function(_9i){var _9j=E(_9i);return new F(function(){return _1s(B(_1q(_9j.a)),_9f,_9j.b);});},_9k=function(_9l){return E(E(_9l).a);},_9m=function(_9n){return new T2(0,_9o,_9n);},_9p=function(_9q,_9r){return new F(function(){return _y(E(_9q).a,_9r);});},_9s=function(_9t,_9u){return new F(function(){return _2D(_9p,_9t,_9u);});},_9v=function(_9w,_9x,_9y){return new F(function(){return _y(E(_9x).a,_9y);});},_9z=new T3(0,_9v,_9k,_9s),_9o=new T(function(){return new T5(0,_9f,_9z,_9m,_9h,_9k);}),_9A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_9B=function(_9C,_9D){return new F(function(){return die(new T(function(){return B(A2(_5F,_9D,_9C));}));});},_9E=function(_9F,_87){return new F(function(){return _9B(_9F,_87);});},_9G=function(_9H,_9I){var _9J=E(_9I);if(!_9J._){return new T2(0,_10,_10);}else{var _9K=_9J.a;if(!B(A1(_9H,_9K))){return new T2(0,_10,_9J);}else{var _9L=new T(function(){var _9M=B(_9G(_9H,_9J.b));return new T2(0,_9M.a,_9M.b);});return new T2(0,new T2(1,_9K,new T(function(){return E(E(_9L).a);})),new T(function(){return E(E(_9L).b);}));}}},_9N=32,_9O=new T(function(){return B(unCStr("\n"));}),_9P=function(_9Q){return (E(_9Q)==124)?false:true;},_9R=function(_9S,_9T){var _9U=B(_9G(_9P,B(unCStr(_9S)))),_9V=_9U.a,_9W=function(_9X,_9Y){var _9Z=new T(function(){var _a0=new T(function(){return B(_y(_9T,new T(function(){return B(_y(_9Y,_9O));},1)));});return B(unAppCStr(": ",_a0));},1);return new F(function(){return _y(_9X,_9Z);});},_a1=E(_9U.b);if(!_a1._){return new F(function(){return _9W(_9V,_10);});}else{if(E(_a1.a)==124){return new F(function(){return _9W(_9V,new T2(1,_9N,_a1.b));});}else{return new F(function(){return _9W(_9V,_10);});}}},_a2=function(_a3){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9R(_a3,_9A));})),_9o);});},_a4=function(_a5){var _a6=function(_a7,_a8){while(1){if(!B(_92(_a7,_a5))){if(!B(_8T(_a7,_a5))){if(!B(_8f(_a7,_a5))){return new F(function(){return _a2("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_a8);}}else{return _a8-1|0;}}else{var _a9=B(_8J(_a7,1)),_aa=_a8+1|0;_a7=_a9;_a8=_aa;continue;}}};return new F(function(){return _a6(_91,0);});},_ab=function(_ac){var _ad=E(_ac);if(!_ad._){var _ae=_ad.a>>>0;if(!_ae){return  -1;}else{var _af=function(_ag,_ah){while(1){if(_ag>=_ae){if(_ag<=_ae){if(_ag!=_ae){return new F(function(){return _a2("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ah);}}else{return _ah-1|0;}}else{var _ai=imul(_ag,2)>>>0,_aj=_ah+1|0;_ag=_ai;_ah=_aj;continue;}}};return new F(function(){return _af(1,0);});}}else{return new F(function(){return _a4(_ad);});}},_ak=function(_al){var _am=E(_al);if(!_am._){var _an=_am.a>>>0;if(!_an){return new T2(0, -1,0);}else{var _ao=function(_ap,_aq){while(1){if(_ap>=_an){if(_ap<=_an){if(_ap!=_an){return new F(function(){return _a2("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_aq);}}else{return _aq-1|0;}}else{var _ar=imul(_ap,2)>>>0,_as=_aq+1|0;_ap=_ar;_aq=_as;continue;}}};return new T2(0,B(_ao(1,0)),(_an&_an-1>>>0)>>>0&4294967295);}}else{var _at=_am.a;return new T2(0,B(_ab(_am)),I_compareInt(I_and(_at,I_sub(_at,I_fromInt(1))),0));}},_au=function(_av,_aw){var _ax=E(_av);if(!_ax._){var _ay=_ax.a,_az=E(_aw);return (_az._==0)?_ay<=_az.a:I_compareInt(_az.a,_ay)>=0;}else{var _aA=_ax.a,_aB=E(_aw);return (_aB._==0)?I_compareInt(_aA,_aB.a)<=0:I_compare(_aA,_aB.a)<=0;}},_aC=function(_aD,_aE){while(1){var _aF=E(_aD);if(!_aF._){var _aG=_aF.a,_aH=E(_aE);if(!_aH._){return new T1(0,(_aG>>>0&_aH.a>>>0)>>>0&4294967295);}else{_aD=new T1(1,I_fromInt(_aG));_aE=_aH;continue;}}else{var _aI=E(_aE);if(!_aI._){_aD=_aF;_aE=new T1(1,I_fromInt(_aI.a));continue;}else{return new T1(1,I_and(_aF.a,_aI.a));}}}},_aJ=function(_aK,_aL){while(1){var _aM=E(_aK);if(!_aM._){var _aN=_aM.a,_aO=E(_aL);if(!_aO._){var _aP=_aO.a,_aQ=subC(_aN,_aP);if(!E(_aQ.b)){return new T1(0,_aQ.a);}else{_aK=new T1(1,I_fromInt(_aN));_aL=new T1(1,I_fromInt(_aP));continue;}}else{_aK=new T1(1,I_fromInt(_aN));_aL=_aO;continue;}}else{var _aR=E(_aL);if(!_aR._){_aK=_aM;_aL=new T1(1,I_fromInt(_aR.a));continue;}else{return new T1(1,I_sub(_aM.a,_aR.a));}}}},_aS=new T1(0,2),_aT=function(_aU,_aV){var _aW=E(_aU);if(!_aW._){var _aX=(_aW.a>>>0&(2<<_aV>>>0)-1>>>0)>>>0,_aY=1<<_aV>>>0;return (_aY<=_aX)?(_aY>=_aX)?1:2:0;}else{var _aZ=B(_aC(_aW,B(_aJ(B(_8J(_aS,_aV)),_91)))),_b0=B(_8J(_91,_aV));return (!B(_8T(_b0,_aZ)))?(!B(_92(_b0,_aZ)))?1:2:0;}},_b1=function(_b2,_b3){while(1){var _b4=E(_b2);if(!_b4._){_b2=new T1(1,I_fromInt(_b4.a));continue;}else{return new T1(1,I_shiftRight(_b4.a,_b3));}}},_b5=function(_b6,_b7,_b8,_b9){var _ba=B(_ak(_b9)),_bb=_ba.a;if(!E(_ba.b)){var _bc=B(_ab(_b8));if(_bc<((_bb+_b6|0)-1|0)){var _bd=_bb+(_b6-_b7|0)|0;if(_bd>0){if(_bd>_bc){if(_bd<=(_bc+1|0)){if(!E(B(_ak(_b8)).b)){return 0;}else{return new F(function(){return _8b(_7p,_b6-_b7|0);});}}else{return 0;}}else{var _be=B(_b1(_b8,_bd));switch(B(_aT(_b8,_bd-1|0))){case 0:return new F(function(){return _8b(_be,_b6-_b7|0);});break;case 1:if(!(B(_8n(_be))&1)){return new F(function(){return _8b(_be,_b6-_b7|0);});}else{return new F(function(){return _8b(B(_8q(_be,_7p)),_b6-_b7|0);});}break;default:return new F(function(){return _8b(B(_8q(_be,_7p)),_b6-_b7|0);});}}}else{return new F(function(){return _8b(_b8,(_b6-_b7|0)-_bd|0);});}}else{if(_bc>=_b7){var _bf=B(_b1(_b8,(_bc+1|0)-_b7|0));switch(B(_aT(_b8,_bc-_b7|0))){case 0:return new F(function(){return _8b(_bf,((_bc-_bb|0)+1|0)-_b7|0);});break;case 2:return new F(function(){return _8b(B(_8q(_bf,_7p)),((_bc-_bb|0)+1|0)-_b7|0);});break;default:if(!(B(_8n(_bf))&1)){return new F(function(){return _8b(_bf,((_bc-_bb|0)+1|0)-_b7|0);});}else{return new F(function(){return _8b(B(_8q(_bf,_7p)),((_bc-_bb|0)+1|0)-_b7|0);});}}}else{return new F(function(){return _8b(_b8, -_bb);});}}}else{var _bg=B(_ab(_b8))-_bb|0,_bh=function(_bi){var _bj=function(_bk,_bl){if(!B(_au(B(_8J(_bl,_b7)),_bk))){return new F(function(){return _8N(_bi-_b7|0,_bk,_bl);});}else{return new F(function(){return _8N((_bi-_b7|0)+1|0,_bk,B(_8J(_bl,1)));});}};if(_bi>=_b7){if(_bi!=_b7){return new F(function(){return _bj(_b8,new T(function(){return B(_8J(_b9,_bi-_b7|0));}));});}else{return new F(function(){return _bj(_b8,_b9);});}}else{return new F(function(){return _bj(new T(function(){return B(_8J(_b8,_b7-_bi|0));}),_b9);});}};if(_b6>_bg){return new F(function(){return _bh(_b6);});}else{return new F(function(){return _bh(_bg);});}}},_bm=new T1(0,2147483647),_bn=new T(function(){return B(_8q(_bm,_91));}),_bo=function(_bp){var _bq=E(_bp);if(!_bq._){var _br=E(_bq.a);return (_br==( -2147483648))?E(_bn):new T1(0, -_br);}else{return new T1(1,I_negate(_bq.a));}},_bs=new T(function(){return 0/0;}),_bt=new T(function(){return  -1/0;}),_bu=new T(function(){return 1/0;}),_bv=0,_bw=function(_bx,_by){if(!B(_8f(_by,_8I))){if(!B(_8f(_bx,_8I))){if(!B(_92(_bx,_8I))){return new F(function(){return _b5( -1021,53,_bx,_by);});}else{return  -B(_b5( -1021,53,B(_bo(_bx)),_by));}}else{return E(_bv);}}else{return (!B(_8f(_bx,_8I)))?(!B(_92(_bx,_8I)))?E(_bu):E(_bt):E(_bs);}},_bz=function(_bA){var _bB=E(_bA);return new F(function(){return _bw(_bB.a,_bB.b);});},_bC=function(_bD){return 1/E(_bD);},_bE=function(_bF){var _bG=E(_bF);return (_bG!=0)?(_bG<=0)? -_bG:E(_bG):E(_bv);},_bH=function(_bI){var _bJ=E(_bI);if(!_bJ._){return _bJ.a;}else{return new F(function(){return I_toNumber(_bJ.a);});}},_bK=function(_bL){return new F(function(){return _bH(_bL);});},_bM=1,_bN= -1,_bO=function(_bP){var _bQ=E(_bP);return (_bQ<=0)?(_bQ>=0)?E(_bQ):E(_bN):E(_bM);},_bR=function(_bS,_bT){return E(_bS)-E(_bT);},_bU=function(_bV){return  -E(_bV);},_bW=function(_bX,_bY){return E(_bX)+E(_bY);},_bZ=function(_c0,_c1){return E(_c0)*E(_c1);},_c2={_:0,a:_bW,b:_bR,c:_bZ,d:_bU,e:_bE,f:_bO,g:_bK},_c3=function(_c4,_c5){return E(_c4)/E(_c5);},_c6=new T4(0,_c2,_c3,_bC,_bz),_c7=new T1(0,1),_c8=function(_c9){return E(E(_c9).a);},_ca=function(_cb){return E(E(_cb).a);},_cc=function(_cd){return E(E(_cd).g);},_ce=function(_cf,_cg){var _ch=E(_cg),_ci=new T(function(){var _cj=B(_c8(_cf)),_ck=B(_ce(_cf,B(A3(_ca,_cj,_ch,new T(function(){return B(A2(_cc,_cj,_c7));})))));return new T2(1,_ck.a,_ck.b);});return new T2(0,_ch,_ci);},_cl=0,_cm=new T(function(){var _cn=B(_ce(_c6,_cl));return new T2(1,_cn.a,_cn.b);}),_co=new T(function(){return B(unCStr("px Unifont"));}),_cp=new T(function(){return B(_I(0,20,_10));}),_cq=new T(function(){return B(_y(_cp,_co));}),_cr=function(_cs,_){return _7f;},_ct=",",_cu="rgba(",_cv=new T(function(){return toJSStr(_10);}),_cw="rgb(",_cx=")",_cy=new T2(1,_cx,_10),_cz=function(_cA){var _cB=E(_cA);if(!_cB._){var _cC=jsCat(new T2(1,_cw,new T2(1,new T(function(){return String(_cB.a);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.b);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.c);}),_cy)))))),E(_cv));return E(_cC);}else{var _cD=jsCat(new T2(1,_cu,new T2(1,new T(function(){return String(_cB.a);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.b);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.c);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.d);}),_cy)))))))),E(_cv));return E(_cD);}},_cE="strokeStyle",_cF="fillStyle",_cG=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_cH=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_cI=function(_cJ,_cK){var _cL=new T(function(){return B(_cz(_cJ));});return function(_cM,_){var _cN=E(_cM),_cO=E(_cF),_cP=E(_cG),_cQ=__app2(_cP,_cN,_cO),_cR=E(_cE),_cS=__app2(_cP,_cN,_cR),_cT=E(_cL),_cU=E(_cH),_cV=__app3(_cU,_cN,_cO,_cT),_cW=__app3(_cU,_cN,_cR,_cT),_cX=B(A2(_cK,_cN,_)),_cY=String(_cQ),_cZ=__app3(_cU,_cN,_cO,_cY),_d0=String(_cS),_d1=__app3(_cU,_cN,_cR,_d0);return new F(function(){return _7g(_);});};},_d2="font",_d3=function(_d4,_d5){var _d6=new T(function(){return toJSStr(E(_d4));});return function(_d7,_){var _d8=E(_d7),_d9=E(_d2),_da=__app2(E(_cG),_d8,_d9),_db=E(_cH),_dc=__app3(_db,_d8,_d9,E(_d6)),_dd=B(A2(_d5,_d8,_)),_de=String(_da),_df=__app3(_db,_d8,_d9,_de);return new F(function(){return _7g(_);});};},_dg=function(_dh,_di,_dj,_dk,_dl){var _dm=new T(function(){return E(_dj)*16;}),_dn=new T(function(){return E(_dk)*20;}),_do=function(_dp,_dq){var _dr=E(_dp);if(!_dr._){return E(_cr);}else{var _ds=E(_dq);if(!_ds._){return E(_cr);}else{var _dt=new T(function(){return B(_do(_dr.b,_ds.b));}),_du=new T(function(){var _dv=new T(function(){var _dw=new T(function(){return B(_7i(new T(function(){return E(_dm)+16*E(_ds.a);}),_dn,new T2(1,_dr.a,_10)));});return B(_d3(_cq,_dw));});return B(_cI(_di,_dv));});return function(_dx,_){var _dy=B(A2(_du,_dx,_));return new F(function(){return A2(_dt,_dx,_);});};}}};return new F(function(){return A3(_do,_dl,_cm,_dh);});},_dz=45,_dA=new T(function(){return B(unCStr("-"));}),_dB=new T2(1,_dz,_dA),_dC=function(_dD){var _dE=E(_dD);return (_dE==1)?E(_dB):new T2(1,_dz,new T(function(){return B(_dC(_dE-1|0));}));},_dF=new T(function(){return B(unCStr(": empty list"));}),_dG=function(_dH){return new F(function(){return err(B(_y(_6W,new T(function(){return B(_y(_dH,_dF));},1))));});},_dI=new T(function(){return B(unCStr("head"));}),_dJ=new T(function(){return B(_dG(_dI));}),_dK=new T(function(){return eval("(function(e){e.width = e.width;})");}),_dL=new T3(0,0,0,0),_dM=new T(function(){return B(_7i(_cl,_cl,_10));}),_dN=32,_dO=new T(function(){return B(unCStr("|"));}),_dP=function(_dQ){var _dR=E(_dQ);return (_dR._==0)?E(_dO):new T2(1,new T(function(){var _dS=E(_dR.a);switch(E(_dS.b)){case 7:return E(_dN);break;case 8:return E(_dN);break;default:return E(_dS.a);}}),new T(function(){return B(_dP(_dR.b));}));},_dT=function(_dU,_dV,_dW,_dX,_dY,_){var _dZ=__app1(E(_dK),_dV),_e0=B(A2(_dM,_dU,_)),_e1=B(unAppCStr("-",new T(function(){var _e2=E(_dY);if(!_e2._){return E(_dJ);}else{var _e3=B(_7a(_e2.a,0));if(0>=_e3){return E(_dA);}else{return B(_dC(_e3));}}}))),_e4=B(A(_dg,[_dU,_dL,_dW,_dX,_e1,_])),_e5=function(_e6,_e7,_e8,_){while(1){var _e9=B((function(_ea,_eb,_ec,_){var _ed=E(_ec);if(!_ed._){return new F(function(){return A(_dg,[_dU,_dL,_ea,_eb,_e1,_]);});}else{var _ee=B(A(_dg,[_dU,_dL,_ea,_eb,B(unAppCStr("|",new T(function(){return B(_dP(_ed.a));}))),_])),_ef=_ea;_e6=_ef;_e7=new T(function(){return E(_eb)+1|0;});_e8=_ed.b;return __continue;}})(_e6,_e7,_e8,_));if(_e9!=__continue){return _e9;}}};return new F(function(){return _e5(_dW,new T(function(){return E(_dX)+1|0;}),_dY,_);});},_eg=new T3(0,153,255,255),_eh=new T2(1,_eg,_10),_ei=new T3(0,255,153,204),_ej=new T2(1,_ei,_eh),_ek=new T3(0,255,204,153),_el=new T2(1,_ek,_ej),_em=new T2(1,_dL,_el),_en=new T(function(){return B(_77(_em,1));}),_eo=new T(function(){return B(_77(_em,2));}),_ep=2,_eq=function(_er){return E(_er).c;},_es=function(_et,_eu,_ev,_){var _ew=__app1(E(_dK),_eu),_ex=B(A2(_dM,_et,_)),_ey=new T(function(){return E(E(E(_ev).b).a);}),_ez=new T(function(){return E(E(_ev).a);}),_eA=B(_dT(_et,_eu,new T(function(){return 26-E(_ey)|0;}),_ep,new T(function(){return E(E(_ez).b);}),_)),_eB=new T(function(){return E(E(_ez).a);});return new F(function(){return A(_dg,[_et,new T(function(){if(E(E(_ez).d)==32){return E(_en);}else{return E(_eo);}}),new T(function(){return ((E(E(_eB).a)+1|0)+26|0)-E(_ey)|0;},1),new T(function(){return (E(E(_eB).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_eq(_ez));}),_10),_]);});},_eC=function(_eD,_eE){while(1){var _eF=E(_eE);if(!_eF._){return __Z;}else{var _eG=_eF.b,_eH=E(_eD);if(_eH==1){return E(_eG);}else{_eD=_eH-1|0;_eE=_eG;continue;}}}},_eI=function(_eJ,_eK){var _eL=E(_eK);if(!_eL._){return __Z;}else{var _eM=_eL.a,_eN=E(_eJ);return (_eN==1)?new T2(1,_eM,_10):new T2(1,_eM,new T(function(){return B(_eI(_eN-1|0,_eL.b));}));}},_eO=function(_eP,_eQ,_eR,_eS){while(1){if(B(_77(new T2(1,_eR,_eS),_eQ))!=_eP){var _eT=_eQ+1|0;_eQ=_eT;continue;}else{if(0>=_eQ){return __Z;}else{return new F(function(){return _eI(_eQ,new T2(1,_eR,_eS));});}}}},_eU=function(_eV,_eW,_eX){var _eY=E(_eX);if(!_eY._){return __Z;}else{var _eZ=E(_eV);if(B(_77(_eY,_eW))!=_eZ){return new F(function(){return _eO(_eZ,_eW+1|0,_eY.a,_eY.b);});}else{if(0>=_eW){return __Z;}else{return new F(function(){return _eI(_eW,_eY);});}}}},_f0=function(_f1,_f2,_f3){var _f4=_f2+1|0;if(_f4>0){return new F(function(){return _eC(_f4,B(_eU(_f1,_f4,_f3)));});}else{return new F(function(){return _eU(_f1,_f4,_f3);});}},_f5=function(_f6,_f7,_f8){while(1){var _f9=E(_f6);if(!_f9._){return E(_f8);}else{var _fa=_f9.a,_fb=E(_f7);if(_fb==1){return E(_fa);}else{_f6=_f9.b;_f7=_fb-1|0;_f8=_fa;continue;}}}},_fc=function(_fd){var _fe=E(_fd);if(!_fe._){return new T2(0,_10,_10);}else{var _ff=E(_fe.a),_fg=new T(function(){var _fh=B(_fc(_fe.b));return new T2(0,_fh.a,_fh.b);});return new T2(0,new T2(1,_ff.a,new T(function(){return E(E(_fg).a);})),new T2(1,_ff.b,new T(function(){return E(E(_fg).b);})));}},_fi=function(_fj,_fk){while(1){var _fl=E(_fj);if(!_fl._){return (E(_fk)._==0)?true:false;}else{var _fm=E(_fk);if(!_fm._){return false;}else{if(E(_fl.a)!=E(_fm.a)){return false;}else{_fj=_fl.b;_fk=_fm.b;continue;}}}}},_fn=function(_fo,_fp){return (!B(_fi(_fo,_fp)))?true:false;},_fq=new T2(0,_fi,_fn),_fr=0,_fs=new T(function(){return B(_a2("Event.hs:(45,1)-(46,68)|function addEvent"));}),_ft=function(_fu,_fv,_fw,_fx,_fy,_fz,_fA,_fB,_fC,_fD,_fE,_fF,_fG,_fH,_fI,_fJ,_fK,_fL,_fM,_fN,_fO,_fP,_fQ){while(1){var _fR=E(_fu);if(!_fR._){return {_:0,a:_fv,b:_fw,c:_fx,d:_fy,e:_fz,f:_fA,g:_fB,h:_fC,i:_fD,j:_fE,k:_fF,l:_fG,m:_fH,n:_fI,o:_fJ,p:_fK,q:_fL,r:_fM,s:_fN,t:_fO,u:_fP,v:_fQ};}else{var _fS=E(_fR.b);if(!_fS._){return E(_fs);}else{var _fT=new T2(1,new T2(0,_fR.a,_fS.a),_fy),_fU=new T2(1,_fr,_fz);_fu=_fS.b;_fy=_fT;_fz=_fU;continue;}}}},_fV=new T(function(){return B(_a2("Event.hs:(66,1)-(67,57)|function addMemory"));}),_fW=function(_fX,_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_ga,_gb,_gc,_gd,_ge,_gf,_gg,_gh,_gi,_gj){while(1){var _gk=E(_fX);if(!_gk._){return {_:0,a:_fY,b:_fZ,c:_g0,d:_g1,e:_g2,f:_g3,g:_g4,h:_g5,i:_g6,j:_g7,k:_g8,l:_g9,m:_ga,n:_gb,o:_gc,p:_gd,q:_ge,r:_gf,s:_gg,t:_gh,u:_gi,v:_gj};}else{var _gl=E(_gk.b);if(!_gl._){return E(_fV);}else{var _gm=new T2(1,new T2(0,_gk.a,_gl.a),_g3);_fX=_gl.b;_g3=_gm;continue;}}}},_gn=function(_go){var _gp=E(_go);if(!_gp._){return new T2(0,_10,_10);}else{var _gq=E(_gp.a),_gr=new T(function(){var _gs=B(_gn(_gp.b));return new T2(0,_gs.a,_gs.b);});return new T2(0,new T2(1,_gq.a,new T(function(){return E(E(_gr).a);})),new T2(1,_gq.b,new T(function(){return E(E(_gr).b);})));}},_gt=function(_gu,_gv,_gw){while(1){var _gx=B((function(_gy,_gz,_gA){var _gB=E(_gA);if(!_gB._){return __Z;}else{var _gC=_gB.b;if(_gz!=E(_gB.a)){var _gD=_gy+1|0,_gE=_gz;_gu=_gD;_gv=_gE;_gw=_gC;return __continue;}else{return new T2(1,_gy,new T(function(){return B(_gt(_gy+1|0,_gz,_gC));}));}}})(_gu,_gv,_gw));if(_gx!=__continue){return _gx;}}},_gF=function(_gG,_gH,_gI){var _gJ=E(_gI);if(!_gJ._){return __Z;}else{var _gK=_gJ.b,_gL=E(_gH);if(_gL!=E(_gJ.a)){return new F(function(){return _gt(_gG+1|0,_gL,_gK);});}else{return new T2(1,_gG,new T(function(){return B(_gt(_gG+1|0,_gL,_gK));}));}}},_gM=function(_gN,_gO,_gP,_gQ){var _gR=E(_gQ);if(!_gR._){return __Z;}else{var _gS=_gR.b;return (!B(_4B(_3M,_gN,_gP)))?new T2(1,_gR.a,new T(function(){return B(_gM(_gN+1|0,_gO,_gP,_gS));})):new T2(1,_gO,new T(function(){return B(_gM(_gN+1|0,_gO,_gP,_gS));}));}},_gT=function(_gU,_gV){var _gW=E(_gU);if(!_gW._){return __Z;}else{var _gX=E(_gV);return (_gX._==0)?__Z:new T2(1,new T2(0,_gW.a,_gX.a),new T(function(){return B(_gT(_gW.b,_gX.b));}));}},_gY=function(_gZ,_h0,_h1){var _h2=E(_h1);if(!_h2._){return __Z;}else{var _h3=new T(function(){var _h4=B(_gn(_h2.a)),_h5=_h4.a,_h6=new T(function(){return B(_gM(0,_h0,new T(function(){return B(_gF(0,_gZ,_h5));}),_h4.b));},1);return B(_gT(_h5,_h6));});return new T2(1,_h3,new T(function(){return B(_gY(_gZ,_h0,_h2.b));}));}},_h7=function(_h8){var _h9=E(_h8);return (_h9._==0)?E(_dJ):E(_h9.a);},_ha=new T(function(){return B(_a2("Event.hs:(39,1)-(42,93)|function changeType"));}),_hb=function(_hc,_hd){while(1){var _he=E(_hc);if(!_he._){return (E(_hd)._==0)?true:false;}else{var _hf=E(_hd);if(!_hf._){return false;}else{if(E(_he.a)!=E(_hf.a)){return false;}else{_hc=_he.b;_hd=_hf.b;continue;}}}}},_hg=new T(function(){return B(unCStr("Mv"));}),_hh=new T(function(){return B(unCStr("Fr"));}),_hi=new T(function(){return B(unCStr("Ex"));}),_hj=new T(function(){return B(unCStr("DF"));}),_hk=new T(function(){return B(unCStr("DB"));}),_hl=new T(function(){return B(unCStr("Cm"));}),_hm=new T(function(){return B(unCStr("Bl"));}),_hn=new T(function(){return B(_a2("Event.hs:36:16-116|case"));}),_ho=new T(function(){return B(unCStr("Wn"));}),_hp=new T(function(){return B(unCStr("Pn"));}),_hq=function(_hr){return (!B(_hb(_hr,_hm)))?(!B(_hb(_hr,_hl)))?(!B(_hb(_hr,_hk)))?(!B(_hb(_hr,_hj)))?(!B(_hb(_hr,_hi)))?(!B(_hb(_hr,_hh)))?(!B(_hb(_hr,_hg)))?(!B(_hb(_hr,_hp)))?(!B(_hb(_hr,_ho)))?E(_hn):5:4:3:0:2:8:7:6:1;},_hs=function(_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_hB,_hC,_hD,_hE,_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP){while(1){var _hQ=B((function(_hR,_hS,_hT,_hU,_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4,_i5,_i6,_i7,_i8,_i9,_ia,_ib,_ic,_id){var _ie=E(_hR);if(!_ie._){return {_:0,a:_hS,b:_hT,c:_hU,d:_hV,e:_hW,f:_hX,g:_hY,h:_hZ,i:_i0,j:_i1,k:_i2,l:_i3,m:_i4,n:_i5,o:_i6,p:_i7,q:_i8,r:_i9,s:_ia,t:_ib,u:_ic,v:_id};}else{var _if=E(_ie.b);if(!_if._){return E(_ha);}else{var _ig=E(_hS),_ih=_hT,_ii=_hU,_ij=_hV,_ik=_hW,_il=_hX,_im=_hY,_in=_hZ,_io=_i0,_ip=_i1,_iq=_i2,_ir=_i3,_is=_i4,_it=_i5,_iu=_i6,_iv=_i7,_iw=_i8,_ix=_i9,_iy=_ia,_iz=_ib,_iA=_ic,_iB=_id;_ht=_if.b;_hu={_:0,a:E(_ig.a),b:E(B(_gY(new T(function(){return B(_h7(_ie.a));}),new T(function(){return B(_hq(_if.a));}),_ig.b))),c:_ig.c,d:_ig.d,e:_ig.e,f:_ig.f,g:E(_ig.g),h:E(_ig.h),i:E(_ig.i)};_hv=_ih;_hw=_ii;_hx=_ij;_hy=_ik;_hz=_il;_hA=_im;_hB=_in;_hC=_io;_hD=_ip;_hE=_iq;_hF=_ir;_hG=_is;_hH=_it;_hI=_iu;_hJ=_iv;_hK=_iw;_hL=_ix;_hM=_iy;_hN=_iz;_hO=_iA;_hP=_iB;return __continue;}}})(_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_hB,_hC,_hD,_hE,_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP));if(_hQ!=__continue){return _hQ;}}},_iC=function(_iD,_iE,_iF){var _iG=E(_iF);return (_iG._==0)?0:(!B(A3(_4z,_iD,_iE,_iG.a)))?1+B(_iC(_iD,_iE,_iG.b))|0:0;},_iH=function(_iI,_iJ){while(1){var _iK=E(_iJ);if(!_iK._){return __Z;}else{var _iL=_iK.b,_iM=E(_iI);if(_iM==1){return E(_iL);}else{_iI=_iM-1|0;_iJ=_iL;continue;}}}},_iN=function(_iO,_iP){var _iQ=new T(function(){var _iR=_iO+1|0;if(_iR>0){return B(_iH(_iR,_iP));}else{return E(_iP);}});if(0>=_iO){return E(_iQ);}else{var _iS=function(_iT,_iU){var _iV=E(_iT);if(!_iV._){return E(_iQ);}else{var _iW=_iV.a,_iX=E(_iU);return (_iX==1)?new T2(1,_iW,_iQ):new T2(1,_iW,new T(function(){return B(_iS(_iV.b,_iX-1|0));}));}};return new F(function(){return _iS(_iP,_iO);});}},_iY=function(_iZ,_j0){return new F(function(){return _iN(E(_iZ),_j0);});},_j1=function(_j2){return E(E(_j2).a);},_j3= -1,_j4=function(_j5,_j6){var _j7=E(_j6);return (_j7._==0)?__Z:new T2(1,new T(function(){return B(A1(_j5,_j7.a));}),new T(function(){return B(_j4(_j5,_j7.b));}));},_j8=function(_j9,_ja,_jb,_jc,_jd,_je,_jf,_jg,_jh,_ji,_jj,_jk,_jl,_jm,_jn,_jo,_jp,_jq,_jr,_js,_jt,_ju,_jv){while(1){var _jw=B((function(_jx,_jy,_jz,_jA,_jB,_jC,_jD,_jE,_jF,_jG,_jH,_jI,_jJ,_jK,_jL,_jM,_jN,_jO,_jP,_jQ,_jR,_jS,_jT){var _jU=E(_jx);if(!_jU._){return {_:0,a:_jy,b:_jz,c:_jA,d:_jB,e:_jC,f:_jD,g:_jE,h:_jF,i:_jG,j:_jH,k:_jI,l:_jJ,m:_jK,n:_jL,o:_jM,p:_jN,q:_jO,r:_jP,s:_jQ,t:_jR,u:_jS,v:_jT};}else{var _jV=_jU.a,_jW=B(_j4(_j1,_jB)),_jX=B(_4B(_fq,_jV,_jW)),_jY=new T(function(){if(!E(_jX)){return E(_j3);}else{return B(_iC(_fq,_jV,_jW));}});if(!E(_jX)){var _jZ=E(_jB);}else{var _jZ=B(_iY(_jY,_jB));}if(!E(_jX)){var _k0=E(_jC);}else{var _k0=B(_iY(_jY,_jC));}var _k1=_jy,_k2=_jz,_k3=_jA,_k4=_jD,_k5=_jE,_k6=_jF,_k7=_jG,_k8=_jH,_k9=_jI,_ka=_jJ,_kb=_jK,_kc=_jL,_kd=_jM,_ke=_jN,_kf=_jO,_kg=_jP,_kh=_jQ,_ki=_jR,_kj=_jS,_kk=_jT;_j9=_jU.b;_ja=_k1;_jb=_k2;_jc=_k3;_jd=_jZ;_je=_k0;_jf=_k4;_jg=_k5;_jh=_k6;_ji=_k7;_jj=_k8;_jk=_k9;_jl=_ka;_jm=_kb;_jn=_kc;_jo=_kd;_jp=_ke;_jq=_kf;_jr=_kg;_js=_kh;_jt=_ki;_ju=_kj;_jv=_kk;return __continue;}})(_j9,_ja,_jb,_jc,_jd,_je,_jf,_jg,_jh,_ji,_jj,_jk,_jl,_jm,_jn,_jo,_jp,_jq,_jr,_js,_jt,_ju,_jv));if(_jw!=__continue){return _jw;}}},_kl=function(_km){var _kn=E(_km);if(!_kn._){return new T2(0,_10,_10);}else{var _ko=E(_kn.a),_kp=new T(function(){var _kq=B(_kl(_kn.b));return new T2(0,_kq.a,_kq.b);});return new T2(0,new T2(1,_ko.a,new T(function(){return E(E(_kp).a);})),new T2(1,_ko.b,new T(function(){return E(E(_kp).b);})));}},_kr=true,_ks=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_kt=function(_ku){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9R(_ku,_ks));})),_9o);});},_kv=function(_kw){return new F(function(){return _kt("Event.hs:80:28-52|(c : d : _)");});},_kx=new T(function(){return B(_kv(_));}),_ky=function(_kz,_kA,_kB){var _kC=E(_kB);if(!_kC._){return new T2(0,new T2(1,_kA,_10),_10);}else{var _kD=E(_kA),_kE=new T(function(){var _kF=B(_ky(_kz,_kC.a,_kC.b));return new T2(0,_kF.a,_kF.b);});return (_kz!=_kD)?new T2(0,new T2(1,_kD,new T(function(){return E(E(_kE).a);})),new T(function(){return E(E(_kE).b);})):new T2(0,_10,new T2(1,new T(function(){return E(E(_kE).a);}),new T(function(){return E(E(_kE).b);})));}},_kG=function(_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_kP,_kQ,_kR,_kS,_kT,_kU,_kV,_kW,_kX,_kY,_kZ,_l0,_l1,_l2,_l3){while(1){var _l4=B((function(_l5,_l6,_l7,_l8,_l9,_la,_lb,_lc,_ld,_le,_lf,_lg,_lh,_li,_lj,_lk,_ll,_lm,_ln,_lo,_lp,_lq,_lr){var _ls=E(_l5);if(!_ls._){return {_:0,a:E(_l6),b:E(_l7),c:E(_l8),d:E(_l9),e:E(_la),f:E(_lb),g:E(_lc),h:_ld,i:_le,j:_lf,k:_lg,l:E(_lh),m:_li,n:E(_lj),o:E(_lk),p:E(_ll),q:E(_kr),r:E(_ln),s:E(_lo),t:E(_kr),u:E(_lq),v:_lr};}else{var _lt=new T(function(){var _lu=E(_ls.a);if(!_lu._){return E(_kx);}else{var _lv=E(_lu.b);if(!_lv._){return E(_kx);}else{var _lw=_lv.a,_lx=_lv.b,_ly=E(_lu.a);if(E(_ly)==44){return new T2(0,_10,new T(function(){return E(B(_ky(44,_lw,_lx)).a);}));}else{var _lz=B(_ky(44,_lw,_lx)),_lA=E(_lz.b);if(!_lA._){return E(_kx);}else{return new T2(0,new T2(1,_ly,_lz.a),_lA.a);}}}}}),_lB=_l6,_lC=_l7,_lD=_l8,_lE=_l9,_lF=_la,_lG=_lb,_lH=_lc,_lI=_ld,_lJ=_le,_lK=_lf,_lL=_lg,_lM=B(_y(_lh,new T2(1,new T2(0,new T(function(){return E(E(_lt).a);}),new T(function(){return E(E(_lt).b);})),_10))),_lN=_li,_lO=_lj,_lP=_lk,_lQ=_ll,_lR=_lm,_lS=_ln,_lT=_lo,_lU=_lp,_lV=_lq,_lW=_lr;_kH=_ls.b;_kI=_lB;_kJ=_lC;_kK=_lD;_kL=_lE;_kM=_lF;_kN=_lG;_kO=_lH;_kP=_lI;_kQ=_lJ;_kR=_lK;_kS=_lL;_kT=_lM;_kU=_lN;_kV=_lO;_kW=_lP;_kX=_lQ;_kY=_lR;_kZ=_lS;_l0=_lT;_l1=_lU;_l2=_lV;_l3=_lW;return __continue;}})(_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_kP,_kQ,_kR,_kS,_kT,_kU,_kV,_kW,_kX,_kY,_kZ,_l0,_l1,_l2,_l3));if(_l4!=__continue){return _l4;}}},_lX=function(_lY,_lZ){while(1){var _m0=E(_lZ);if(!_m0._){return __Z;}else{var _m1=_m0.b,_m2=E(_lY);if(_m2==1){return E(_m1);}else{_lY=_m2-1|0;_lZ=_m1;continue;}}}},_m3=function(_m4,_m5){while(1){var _m6=E(_m5);if(!_m6._){return __Z;}else{var _m7=_m6.b,_m8=E(_m4);if(_m8==1){return E(_m7);}else{_m4=_m8-1|0;_m5=_m7;continue;}}}},_m9=function(_ma,_mb,_mc,_md,_me){var _mf=new T(function(){var _mg=E(_ma),_mh=new T(function(){return B(_77(_me,_mb));}),_mi=new T2(1,new T2(0,_mc,_md),new T(function(){var _mj=_mg+1|0;if(_mj>0){return B(_m3(_mj,_mh));}else{return E(_mh);}}));if(0>=_mg){return E(_mi);}else{var _mk=function(_ml,_mm){var _mn=E(_ml);if(!_mn._){return E(_mi);}else{var _mo=_mn.a,_mp=E(_mm);return (_mp==1)?new T2(1,_mo,_mi):new T2(1,_mo,new T(function(){return B(_mk(_mn.b,_mp-1|0));}));}};return B(_mk(_mh,_mg));}}),_mq=new T2(1,_mf,new T(function(){var _mr=_mb+1|0;if(_mr>0){return B(_lX(_mr,_me));}else{return E(_me);}}));if(0>=_mb){return E(_mq);}else{var _ms=function(_mt,_mu){var _mv=E(_mt);if(!_mv._){return E(_mq);}else{var _mw=_mv.a,_mx=E(_mu);return (_mx==1)?new T2(1,_mw,_mq):new T2(1,_mw,new T(function(){return B(_ms(_mv.b,_mx-1|0));}));}};return new F(function(){return _ms(_me,_mb);});}},_my=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_mz=new T(function(){return B(err(_my));}),_mA=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_mB=new T(function(){return B(err(_mA));}),_mC=function(_mD){return new F(function(){return _kt("Event.hs:29:27-53|(x\' : y\' : _)");});},_mE=new T(function(){return B(_mC(_));}),_mF=function(_mG){return new F(function(){return _kt("Event.hs:30:27-55|(chs : tps : _)");});},_mH=new T(function(){return B(_mF(_));}),_mI=new T(function(){return B(_a2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_mJ=function(_mK,_mL){while(1){var _mM=B((function(_mN,_mO){var _mP=E(_mN);switch(_mP._){case 0:var _mQ=E(_mO);if(!_mQ._){return __Z;}else{_mK=B(A1(_mP.a,_mQ.a));_mL=_mQ.b;return __continue;}break;case 1:var _mR=B(A1(_mP.a,_mO)),_mS=_mO;_mK=_mR;_mL=_mS;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_mP.a,_mO),new T(function(){return B(_mJ(_mP.b,_mO));}));default:return E(_mP.a);}})(_mK,_mL));if(_mM!=__continue){return _mM;}}},_mT=function(_mU,_mV){var _mW=function(_mX){var _mY=E(_mV);if(_mY._==3){return new T2(3,_mY.a,new T(function(){return B(_mT(_mU,_mY.b));}));}else{var _mZ=E(_mU);if(_mZ._==2){return E(_mY);}else{var _n0=E(_mY);if(_n0._==2){return E(_mZ);}else{var _n1=function(_n2){var _n3=E(_n0);if(_n3._==4){var _n4=function(_n5){return new T1(4,new T(function(){return B(_y(B(_mJ(_mZ,_n5)),_n3.a));}));};return new T1(1,_n4);}else{var _n6=E(_mZ);if(_n6._==1){var _n7=_n6.a,_n8=E(_n3);if(!_n8._){return new T1(1,function(_n9){return new F(function(){return _mT(B(A1(_n7,_n9)),_n8);});});}else{var _na=function(_nb){return new F(function(){return _mT(B(A1(_n7,_nb)),new T(function(){return B(A1(_n8.a,_nb));}));});};return new T1(1,_na);}}else{var _nc=E(_n3);if(!_nc._){return E(_mI);}else{var _nd=function(_ne){return new F(function(){return _mT(_n6,new T(function(){return B(A1(_nc.a,_ne));}));});};return new T1(1,_nd);}}}},_nf=E(_mZ);switch(_nf._){case 1:var _ng=E(_n0);if(_ng._==4){var _nh=function(_ni){return new T1(4,new T(function(){return B(_y(B(_mJ(B(A1(_nf.a,_ni)),_ni)),_ng.a));}));};return new T1(1,_nh);}else{return new F(function(){return _n1(_);});}break;case 4:var _nj=_nf.a,_nk=E(_n0);switch(_nk._){case 0:var _nl=function(_nm){var _nn=new T(function(){return B(_y(_nj,new T(function(){return B(_mJ(_nk,_nm));},1)));});return new T1(4,_nn);};return new T1(1,_nl);case 1:var _no=function(_np){var _nq=new T(function(){return B(_y(_nj,new T(function(){return B(_mJ(B(A1(_nk.a,_np)),_np));},1)));});return new T1(4,_nq);};return new T1(1,_no);default:return new T1(4,new T(function(){return B(_y(_nj,_nk.a));}));}break;default:return new F(function(){return _n1(_);});}}}}},_nr=E(_mU);switch(_nr._){case 0:var _ns=E(_mV);if(!_ns._){var _nt=function(_nu){return new F(function(){return _mT(B(A1(_nr.a,_nu)),new T(function(){return B(A1(_ns.a,_nu));}));});};return new T1(0,_nt);}else{return new F(function(){return _mW(_);});}break;case 3:return new T2(3,_nr.a,new T(function(){return B(_mT(_nr.b,_mV));}));default:return new F(function(){return _mW(_);});}},_nv=new T(function(){return B(unCStr("("));}),_nw=new T(function(){return B(unCStr(")"));}),_nx=function(_ny,_nz){var _nA=E(_ny);switch(_nA._){case 0:return new T1(0,function(_nB){return new F(function(){return _nx(B(A1(_nA.a,_nB)),_nz);});});case 1:return new T1(1,function(_nC){return new F(function(){return _nx(B(A1(_nA.a,_nC)),_nz);});});case 2:return new T0(2);case 3:return new F(function(){return _mT(B(A1(_nz,_nA.a)),new T(function(){return B(_nx(_nA.b,_nz));}));});break;default:var _nD=function(_nE){var _nF=E(_nE);if(!_nF._){return __Z;}else{var _nG=E(_nF.a);return new F(function(){return _y(B(_mJ(B(A1(_nz,_nG.a)),_nG.b)),new T(function(){return B(_nD(_nF.b));},1));});}},_nH=B(_nD(_nA.a));return (_nH._==0)?new T0(2):new T1(4,_nH);}},_nI=new T0(2),_nJ=function(_nK){return new T2(3,_nK,_nI);},_nL=function(_nM,_nN){var _nO=E(_nM);if(!_nO){return new F(function(){return A1(_nN,_7f);});}else{var _nP=new T(function(){return B(_nL(_nO-1|0,_nN));});return new T1(0,function(_nQ){return E(_nP);});}},_nR=function(_nS,_nT,_nU){var _nV=new T(function(){return B(A1(_nS,_nJ));}),_nW=function(_nX,_nY,_nZ,_o0){while(1){var _o1=B((function(_o2,_o3,_o4,_o5){var _o6=E(_o2);switch(_o6._){case 0:var _o7=E(_o3);if(!_o7._){return new F(function(){return A1(_nT,_o5);});}else{var _o8=_o4+1|0,_o9=_o5;_nX=B(A1(_o6.a,_o7.a));_nY=_o7.b;_nZ=_o8;_o0=_o9;return __continue;}break;case 1:var _oa=B(A1(_o6.a,_o3)),_ob=_o3,_o8=_o4,_o9=_o5;_nX=_oa;_nY=_ob;_nZ=_o8;_o0=_o9;return __continue;case 2:return new F(function(){return A1(_nT,_o5);});break;case 3:var _oc=new T(function(){return B(_nx(_o6,_o5));});return new F(function(){return _nL(_o4,function(_od){return E(_oc);});});break;default:return new F(function(){return _nx(_o6,_o5);});}})(_nX,_nY,_nZ,_o0));if(_o1!=__continue){return _o1;}}};return function(_oe){return new F(function(){return _nW(_nV,_oe,0,_nU);});};},_of=function(_og){return new F(function(){return A1(_og,_10);});},_oh=function(_oi,_oj){var _ok=function(_ol){var _om=E(_ol);if(!_om._){return E(_of);}else{var _on=_om.a;if(!B(A1(_oi,_on))){return E(_of);}else{var _oo=new T(function(){return B(_ok(_om.b));}),_op=function(_oq){var _or=new T(function(){return B(A1(_oo,function(_os){return new F(function(){return A1(_oq,new T2(1,_on,_os));});}));});return new T1(0,function(_ot){return E(_or);});};return E(_op);}}};return function(_ou){return new F(function(){return A2(_ok,_ou,_oj);});};},_ov=new T0(6),_ow=new T(function(){return B(unCStr("valDig: Bad base"));}),_ox=new T(function(){return B(err(_ow));}),_oy=function(_oz,_oA){var _oB=function(_oC,_oD){var _oE=E(_oC);if(!_oE._){var _oF=new T(function(){return B(A1(_oD,_10));});return function(_oG){return new F(function(){return A1(_oG,_oF);});};}else{var _oH=E(_oE.a),_oI=function(_oJ){var _oK=new T(function(){return B(_oB(_oE.b,function(_oL){return new F(function(){return A1(_oD,new T2(1,_oJ,_oL));});}));}),_oM=function(_oN){var _oO=new T(function(){return B(A1(_oK,_oN));});return new T1(0,function(_oP){return E(_oO);});};return E(_oM);};switch(E(_oz)){case 8:if(48>_oH){var _oQ=new T(function(){return B(A1(_oD,_10));});return function(_oR){return new F(function(){return A1(_oR,_oQ);});};}else{if(_oH>55){var _oS=new T(function(){return B(A1(_oD,_10));});return function(_oT){return new F(function(){return A1(_oT,_oS);});};}else{return new F(function(){return _oI(_oH-48|0);});}}break;case 10:if(48>_oH){var _oU=new T(function(){return B(A1(_oD,_10));});return function(_oV){return new F(function(){return A1(_oV,_oU);});};}else{if(_oH>57){var _oW=new T(function(){return B(A1(_oD,_10));});return function(_oX){return new F(function(){return A1(_oX,_oW);});};}else{return new F(function(){return _oI(_oH-48|0);});}}break;case 16:if(48>_oH){if(97>_oH){if(65>_oH){var _oY=new T(function(){return B(A1(_oD,_10));});return function(_oZ){return new F(function(){return A1(_oZ,_oY);});};}else{if(_oH>70){var _p0=new T(function(){return B(A1(_oD,_10));});return function(_p1){return new F(function(){return A1(_p1,_p0);});};}else{return new F(function(){return _oI((_oH-65|0)+10|0);});}}}else{if(_oH>102){if(65>_oH){var _p2=new T(function(){return B(A1(_oD,_10));});return function(_p3){return new F(function(){return A1(_p3,_p2);});};}else{if(_oH>70){var _p4=new T(function(){return B(A1(_oD,_10));});return function(_p5){return new F(function(){return A1(_p5,_p4);});};}else{return new F(function(){return _oI((_oH-65|0)+10|0);});}}}else{return new F(function(){return _oI((_oH-97|0)+10|0);});}}}else{if(_oH>57){if(97>_oH){if(65>_oH){var _p6=new T(function(){return B(A1(_oD,_10));});return function(_p7){return new F(function(){return A1(_p7,_p6);});};}else{if(_oH>70){var _p8=new T(function(){return B(A1(_oD,_10));});return function(_p9){return new F(function(){return A1(_p9,_p8);});};}else{return new F(function(){return _oI((_oH-65|0)+10|0);});}}}else{if(_oH>102){if(65>_oH){var _pa=new T(function(){return B(A1(_oD,_10));});return function(_pb){return new F(function(){return A1(_pb,_pa);});};}else{if(_oH>70){var _pc=new T(function(){return B(A1(_oD,_10));});return function(_pd){return new F(function(){return A1(_pd,_pc);});};}else{return new F(function(){return _oI((_oH-65|0)+10|0);});}}}else{return new F(function(){return _oI((_oH-97|0)+10|0);});}}}else{return new F(function(){return _oI(_oH-48|0);});}}break;default:return E(_ox);}}},_pe=function(_pf){var _pg=E(_pf);if(!_pg._){return new T0(2);}else{return new F(function(){return A1(_oA,_pg);});}};return function(_ph){return new F(function(){return A3(_oB,_ph,_5V,_pe);});};},_pi=16,_pj=8,_pk=function(_pl){var _pm=function(_pn){return new F(function(){return A1(_pl,new T1(5,new T2(0,_pj,_pn)));});},_po=function(_pp){return new F(function(){return A1(_pl,new T1(5,new T2(0,_pi,_pp)));});},_pq=function(_pr){switch(E(_pr)){case 79:return new T1(1,B(_oy(_pj,_pm)));case 88:return new T1(1,B(_oy(_pi,_po)));case 111:return new T1(1,B(_oy(_pj,_pm)));case 120:return new T1(1,B(_oy(_pi,_po)));default:return new T0(2);}};return function(_ps){return (E(_ps)==48)?E(new T1(0,_pq)):new T0(2);};},_pt=function(_pu){return new T1(0,B(_pk(_pu)));},_pv=function(_pw){return new F(function(){return A1(_pw,_0);});},_px=function(_py){return new F(function(){return A1(_py,_0);});},_pz=10,_pA=new T1(0,10),_pB=function(_pC){return new T1(0,_pC);},_pD=function(_pE){return new F(function(){return _pB(E(_pE));});},_pF=new T(function(){return B(unCStr("this should not happen"));}),_pG=new T(function(){return B(err(_pF));}),_pH=function(_pI,_pJ){while(1){var _pK=E(_pI);if(!_pK._){var _pL=_pK.a,_pM=E(_pJ);if(!_pM._){var _pN=_pM.a;if(!(imul(_pL,_pN)|0)){return new T1(0,imul(_pL,_pN)|0);}else{_pI=new T1(1,I_fromInt(_pL));_pJ=new T1(1,I_fromInt(_pN));continue;}}else{_pI=new T1(1,I_fromInt(_pL));_pJ=_pM;continue;}}else{var _pO=E(_pJ);if(!_pO._){_pI=_pK;_pJ=new T1(1,I_fromInt(_pO.a));continue;}else{return new T1(1,I_mul(_pK.a,_pO.a));}}}},_pP=function(_pQ,_pR){var _pS=E(_pR);if(!_pS._){return __Z;}else{var _pT=E(_pS.b);return (_pT._==0)?E(_pG):new T2(1,B(_8q(B(_pH(_pS.a,_pQ)),_pT.a)),new T(function(){return B(_pP(_pQ,_pT.b));}));}},_pU=new T1(0,0),_pV=function(_pW,_pX,_pY){while(1){var _pZ=B((function(_q0,_q1,_q2){var _q3=E(_q2);if(!_q3._){return E(_pU);}else{if(!E(_q3.b)._){return E(_q3.a);}else{var _q4=E(_q1);if(_q4<=40){var _q5=function(_q6,_q7){while(1){var _q8=E(_q7);if(!_q8._){return E(_q6);}else{var _q9=B(_8q(B(_pH(_q6,_q0)),_q8.a));_q6=_q9;_q7=_q8.b;continue;}}};return new F(function(){return _q5(_pU,_q3);});}else{var _qa=B(_pH(_q0,_q0));if(!(_q4%2)){var _qb=B(_pP(_q0,_q3));_pW=_qa;_pX=quot(_q4+1|0,2);_pY=_qb;return __continue;}else{var _qb=B(_pP(_q0,new T2(1,_pU,_q3)));_pW=_qa;_pX=quot(_q4+1|0,2);_pY=_qb;return __continue;}}}}})(_pW,_pX,_pY));if(_pZ!=__continue){return _pZ;}}},_qc=function(_qd,_qe){return new F(function(){return _pV(_qd,new T(function(){return B(_7a(_qe,0));},1),B(_j4(_pD,_qe)));});},_qf=function(_qg){var _qh=new T(function(){var _qi=new T(function(){var _qj=function(_qk){return new F(function(){return A1(_qg,new T1(1,new T(function(){return B(_qc(_pA,_qk));})));});};return new T1(1,B(_oy(_pz,_qj)));}),_ql=function(_qm){if(E(_qm)==43){var _qn=function(_qo){return new F(function(){return A1(_qg,new T1(1,new T(function(){return B(_qc(_pA,_qo));})));});};return new T1(1,B(_oy(_pz,_qn)));}else{return new T0(2);}},_qp=function(_qq){if(E(_qq)==45){var _qr=function(_qs){return new F(function(){return A1(_qg,new T1(1,new T(function(){return B(_bo(B(_qc(_pA,_qs))));})));});};return new T1(1,B(_oy(_pz,_qr)));}else{return new T0(2);}};return B(_mT(B(_mT(new T1(0,_qp),new T1(0,_ql))),_qi));});return new F(function(){return _mT(new T1(0,function(_qt){return (E(_qt)==101)?E(_qh):new T0(2);}),new T1(0,function(_qu){return (E(_qu)==69)?E(_qh):new T0(2);}));});},_qv=function(_qw){var _qx=function(_qy){return new F(function(){return A1(_qw,new T1(1,_qy));});};return function(_qz){return (E(_qz)==46)?new T1(1,B(_oy(_pz,_qx))):new T0(2);};},_qA=function(_qB){return new T1(0,B(_qv(_qB)));},_qC=function(_qD){var _qE=function(_qF){var _qG=function(_qH){return new T1(1,B(_nR(_qf,_pv,function(_qI){return new F(function(){return A1(_qD,new T1(5,new T3(1,_qF,_qH,_qI)));});})));};return new T1(1,B(_nR(_qA,_px,_qG)));};return new F(function(){return _oy(_pz,_qE);});},_qJ=function(_qK){return new T1(1,B(_qC(_qK)));},_qL=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_qM=function(_qN){return new F(function(){return _4B(_6f,_qN,_qL);});},_qO=false,_qP=function(_qQ){var _qR=new T(function(){return B(A1(_qQ,_pj));}),_qS=new T(function(){return B(A1(_qQ,_pi));});return function(_qT){switch(E(_qT)){case 79:return E(_qR);case 88:return E(_qS);case 111:return E(_qR);case 120:return E(_qS);default:return new T0(2);}};},_qU=function(_qV){return new T1(0,B(_qP(_qV)));},_qW=function(_qX){return new F(function(){return A1(_qX,_pz);});},_qY=function(_qZ){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_I(9,_qZ,_10));}))));});},_r0=function(_r1){return new T0(2);},_r2=function(_r3){var _r4=E(_r3);if(!_r4._){return E(_r0);}else{var _r5=_r4.a,_r6=E(_r4.b);if(!_r6._){return E(_r5);}else{var _r7=new T(function(){return B(_r2(_r6));}),_r8=function(_r9){return new F(function(){return _mT(B(A1(_r5,_r9)),new T(function(){return B(A1(_r7,_r9));}));});};return E(_r8);}}},_ra=function(_rb,_rc){var _rd=function(_re,_rf,_rg){var _rh=E(_re);if(!_rh._){return new F(function(){return A1(_rg,_rb);});}else{var _ri=E(_rf);if(!_ri._){return new T0(2);}else{if(E(_rh.a)!=E(_ri.a)){return new T0(2);}else{var _rj=new T(function(){return B(_rd(_rh.b,_ri.b,_rg));});return new T1(0,function(_rk){return E(_rj);});}}}};return function(_rl){return new F(function(){return _rd(_rb,_rl,_rc);});};},_rm=new T(function(){return B(unCStr("SO"));}),_rn=14,_ro=function(_rp){var _rq=new T(function(){return B(A1(_rp,_rn));});return new T1(1,B(_ra(_rm,function(_rr){return E(_rq);})));},_rs=new T(function(){return B(unCStr("SOH"));}),_rt=1,_ru=function(_rv){var _rw=new T(function(){return B(A1(_rv,_rt));});return new T1(1,B(_ra(_rs,function(_rx){return E(_rw);})));},_ry=function(_rz){return new T1(1,B(_nR(_ru,_ro,_rz)));},_rA=new T(function(){return B(unCStr("NUL"));}),_rB=0,_rC=function(_rD){var _rE=new T(function(){return B(A1(_rD,_rB));});return new T1(1,B(_ra(_rA,function(_rF){return E(_rE);})));},_rG=new T(function(){return B(unCStr("STX"));}),_rH=2,_rI=function(_rJ){var _rK=new T(function(){return B(A1(_rJ,_rH));});return new T1(1,B(_ra(_rG,function(_rL){return E(_rK);})));},_rM=new T(function(){return B(unCStr("ETX"));}),_rN=3,_rO=function(_rP){var _rQ=new T(function(){return B(A1(_rP,_rN));});return new T1(1,B(_ra(_rM,function(_rR){return E(_rQ);})));},_rS=new T(function(){return B(unCStr("EOT"));}),_rT=4,_rU=function(_rV){var _rW=new T(function(){return B(A1(_rV,_rT));});return new T1(1,B(_ra(_rS,function(_rX){return E(_rW);})));},_rY=new T(function(){return B(unCStr("ENQ"));}),_rZ=5,_s0=function(_s1){var _s2=new T(function(){return B(A1(_s1,_rZ));});return new T1(1,B(_ra(_rY,function(_s3){return E(_s2);})));},_s4=new T(function(){return B(unCStr("ACK"));}),_s5=6,_s6=function(_s7){var _s8=new T(function(){return B(A1(_s7,_s5));});return new T1(1,B(_ra(_s4,function(_s9){return E(_s8);})));},_sa=new T(function(){return B(unCStr("BEL"));}),_sb=7,_sc=function(_sd){var _se=new T(function(){return B(A1(_sd,_sb));});return new T1(1,B(_ra(_sa,function(_sf){return E(_se);})));},_sg=new T(function(){return B(unCStr("BS"));}),_sh=8,_si=function(_sj){var _sk=new T(function(){return B(A1(_sj,_sh));});return new T1(1,B(_ra(_sg,function(_sl){return E(_sk);})));},_sm=new T(function(){return B(unCStr("HT"));}),_sn=9,_so=function(_sp){var _sq=new T(function(){return B(A1(_sp,_sn));});return new T1(1,B(_ra(_sm,function(_sr){return E(_sq);})));},_ss=new T(function(){return B(unCStr("LF"));}),_st=10,_su=function(_sv){var _sw=new T(function(){return B(A1(_sv,_st));});return new T1(1,B(_ra(_ss,function(_sx){return E(_sw);})));},_sy=new T(function(){return B(unCStr("VT"));}),_sz=11,_sA=function(_sB){var _sC=new T(function(){return B(A1(_sB,_sz));});return new T1(1,B(_ra(_sy,function(_sD){return E(_sC);})));},_sE=new T(function(){return B(unCStr("FF"));}),_sF=12,_sG=function(_sH){var _sI=new T(function(){return B(A1(_sH,_sF));});return new T1(1,B(_ra(_sE,function(_sJ){return E(_sI);})));},_sK=new T(function(){return B(unCStr("CR"));}),_sL=13,_sM=function(_sN){var _sO=new T(function(){return B(A1(_sN,_sL));});return new T1(1,B(_ra(_sK,function(_sP){return E(_sO);})));},_sQ=new T(function(){return B(unCStr("SI"));}),_sR=15,_sS=function(_sT){var _sU=new T(function(){return B(A1(_sT,_sR));});return new T1(1,B(_ra(_sQ,function(_sV){return E(_sU);})));},_sW=new T(function(){return B(unCStr("DLE"));}),_sX=16,_sY=function(_sZ){var _t0=new T(function(){return B(A1(_sZ,_sX));});return new T1(1,B(_ra(_sW,function(_t1){return E(_t0);})));},_t2=new T(function(){return B(unCStr("DC1"));}),_t3=17,_t4=function(_t5){var _t6=new T(function(){return B(A1(_t5,_t3));});return new T1(1,B(_ra(_t2,function(_t7){return E(_t6);})));},_t8=new T(function(){return B(unCStr("DC2"));}),_t9=18,_ta=function(_tb){var _tc=new T(function(){return B(A1(_tb,_t9));});return new T1(1,B(_ra(_t8,function(_td){return E(_tc);})));},_te=new T(function(){return B(unCStr("DC3"));}),_tf=19,_tg=function(_th){var _ti=new T(function(){return B(A1(_th,_tf));});return new T1(1,B(_ra(_te,function(_tj){return E(_ti);})));},_tk=new T(function(){return B(unCStr("DC4"));}),_tl=20,_tm=function(_tn){var _to=new T(function(){return B(A1(_tn,_tl));});return new T1(1,B(_ra(_tk,function(_tp){return E(_to);})));},_tq=new T(function(){return B(unCStr("NAK"));}),_tr=21,_ts=function(_tt){var _tu=new T(function(){return B(A1(_tt,_tr));});return new T1(1,B(_ra(_tq,function(_tv){return E(_tu);})));},_tw=new T(function(){return B(unCStr("SYN"));}),_tx=22,_ty=function(_tz){var _tA=new T(function(){return B(A1(_tz,_tx));});return new T1(1,B(_ra(_tw,function(_tB){return E(_tA);})));},_tC=new T(function(){return B(unCStr("ETB"));}),_tD=23,_tE=function(_tF){var _tG=new T(function(){return B(A1(_tF,_tD));});return new T1(1,B(_ra(_tC,function(_tH){return E(_tG);})));},_tI=new T(function(){return B(unCStr("CAN"));}),_tJ=24,_tK=function(_tL){var _tM=new T(function(){return B(A1(_tL,_tJ));});return new T1(1,B(_ra(_tI,function(_tN){return E(_tM);})));},_tO=new T(function(){return B(unCStr("EM"));}),_tP=25,_tQ=function(_tR){var _tS=new T(function(){return B(A1(_tR,_tP));});return new T1(1,B(_ra(_tO,function(_tT){return E(_tS);})));},_tU=new T(function(){return B(unCStr("SUB"));}),_tV=26,_tW=function(_tX){var _tY=new T(function(){return B(A1(_tX,_tV));});return new T1(1,B(_ra(_tU,function(_tZ){return E(_tY);})));},_u0=new T(function(){return B(unCStr("ESC"));}),_u1=27,_u2=function(_u3){var _u4=new T(function(){return B(A1(_u3,_u1));});return new T1(1,B(_ra(_u0,function(_u5){return E(_u4);})));},_u6=new T(function(){return B(unCStr("FS"));}),_u7=28,_u8=function(_u9){var _ua=new T(function(){return B(A1(_u9,_u7));});return new T1(1,B(_ra(_u6,function(_ub){return E(_ua);})));},_uc=new T(function(){return B(unCStr("GS"));}),_ud=29,_ue=function(_uf){var _ug=new T(function(){return B(A1(_uf,_ud));});return new T1(1,B(_ra(_uc,function(_uh){return E(_ug);})));},_ui=new T(function(){return B(unCStr("RS"));}),_uj=30,_uk=function(_ul){var _um=new T(function(){return B(A1(_ul,_uj));});return new T1(1,B(_ra(_ui,function(_un){return E(_um);})));},_uo=new T(function(){return B(unCStr("US"));}),_up=31,_uq=function(_ur){var _us=new T(function(){return B(A1(_ur,_up));});return new T1(1,B(_ra(_uo,function(_ut){return E(_us);})));},_uu=new T(function(){return B(unCStr("SP"));}),_uv=32,_uw=function(_ux){var _uy=new T(function(){return B(A1(_ux,_uv));});return new T1(1,B(_ra(_uu,function(_uz){return E(_uy);})));},_uA=new T(function(){return B(unCStr("DEL"));}),_uB=127,_uC=function(_uD){var _uE=new T(function(){return B(A1(_uD,_uB));});return new T1(1,B(_ra(_uA,function(_uF){return E(_uE);})));},_uG=new T2(1,_uC,_10),_uH=new T2(1,_uw,_uG),_uI=new T2(1,_uq,_uH),_uJ=new T2(1,_uk,_uI),_uK=new T2(1,_ue,_uJ),_uL=new T2(1,_u8,_uK),_uM=new T2(1,_u2,_uL),_uN=new T2(1,_tW,_uM),_uO=new T2(1,_tQ,_uN),_uP=new T2(1,_tK,_uO),_uQ=new T2(1,_tE,_uP),_uR=new T2(1,_ty,_uQ),_uS=new T2(1,_ts,_uR),_uT=new T2(1,_tm,_uS),_uU=new T2(1,_tg,_uT),_uV=new T2(1,_ta,_uU),_uW=new T2(1,_t4,_uV),_uX=new T2(1,_sY,_uW),_uY=new T2(1,_sS,_uX),_uZ=new T2(1,_sM,_uY),_v0=new T2(1,_sG,_uZ),_v1=new T2(1,_sA,_v0),_v2=new T2(1,_su,_v1),_v3=new T2(1,_so,_v2),_v4=new T2(1,_si,_v3),_v5=new T2(1,_sc,_v4),_v6=new T2(1,_s6,_v5),_v7=new T2(1,_s0,_v6),_v8=new T2(1,_rU,_v7),_v9=new T2(1,_rO,_v8),_va=new T2(1,_rI,_v9),_vb=new T2(1,_rC,_va),_vc=new T2(1,_ry,_vb),_vd=new T(function(){return B(_r2(_vc));}),_ve=34,_vf=new T1(0,1114111),_vg=92,_vh=39,_vi=function(_vj){var _vk=new T(function(){return B(A1(_vj,_sb));}),_vl=new T(function(){return B(A1(_vj,_sh));}),_vm=new T(function(){return B(A1(_vj,_sn));}),_vn=new T(function(){return B(A1(_vj,_st));}),_vo=new T(function(){return B(A1(_vj,_sz));}),_vp=new T(function(){return B(A1(_vj,_sF));}),_vq=new T(function(){return B(A1(_vj,_sL));}),_vr=new T(function(){return B(A1(_vj,_vg));}),_vs=new T(function(){return B(A1(_vj,_vh));}),_vt=new T(function(){return B(A1(_vj,_ve));}),_vu=new T(function(){var _vv=function(_vw){var _vx=new T(function(){return B(_pB(E(_vw)));}),_vy=function(_vz){var _vA=B(_qc(_vx,_vz));if(!B(_au(_vA,_vf))){return new T0(2);}else{return new F(function(){return A1(_vj,new T(function(){var _vB=B(_8n(_vA));if(_vB>>>0>1114111){return B(_qY(_vB));}else{return _vB;}}));});}};return new T1(1,B(_oy(_vw,_vy)));},_vC=new T(function(){var _vD=new T(function(){return B(A1(_vj,_up));}),_vE=new T(function(){return B(A1(_vj,_uj));}),_vF=new T(function(){return B(A1(_vj,_ud));}),_vG=new T(function(){return B(A1(_vj,_u7));}),_vH=new T(function(){return B(A1(_vj,_u1));}),_vI=new T(function(){return B(A1(_vj,_tV));}),_vJ=new T(function(){return B(A1(_vj,_tP));}),_vK=new T(function(){return B(A1(_vj,_tJ));}),_vL=new T(function(){return B(A1(_vj,_tD));}),_vM=new T(function(){return B(A1(_vj,_tx));}),_vN=new T(function(){return B(A1(_vj,_tr));}),_vO=new T(function(){return B(A1(_vj,_tl));}),_vP=new T(function(){return B(A1(_vj,_tf));}),_vQ=new T(function(){return B(A1(_vj,_t9));}),_vR=new T(function(){return B(A1(_vj,_t3));}),_vS=new T(function(){return B(A1(_vj,_sX));}),_vT=new T(function(){return B(A1(_vj,_sR));}),_vU=new T(function(){return B(A1(_vj,_rn));}),_vV=new T(function(){return B(A1(_vj,_s5));}),_vW=new T(function(){return B(A1(_vj,_rZ));}),_vX=new T(function(){return B(A1(_vj,_rT));}),_vY=new T(function(){return B(A1(_vj,_rN));}),_vZ=new T(function(){return B(A1(_vj,_rH));}),_w0=new T(function(){return B(A1(_vj,_rt));}),_w1=new T(function(){return B(A1(_vj,_rB));}),_w2=function(_w3){switch(E(_w3)){case 64:return E(_w1);case 65:return E(_w0);case 66:return E(_vZ);case 67:return E(_vY);case 68:return E(_vX);case 69:return E(_vW);case 70:return E(_vV);case 71:return E(_vk);case 72:return E(_vl);case 73:return E(_vm);case 74:return E(_vn);case 75:return E(_vo);case 76:return E(_vp);case 77:return E(_vq);case 78:return E(_vU);case 79:return E(_vT);case 80:return E(_vS);case 81:return E(_vR);case 82:return E(_vQ);case 83:return E(_vP);case 84:return E(_vO);case 85:return E(_vN);case 86:return E(_vM);case 87:return E(_vL);case 88:return E(_vK);case 89:return E(_vJ);case 90:return E(_vI);case 91:return E(_vH);case 92:return E(_vG);case 93:return E(_vF);case 94:return E(_vE);case 95:return E(_vD);default:return new T0(2);}};return B(_mT(new T1(0,function(_w4){return (E(_w4)==94)?E(new T1(0,_w2)):new T0(2);}),new T(function(){return B(A1(_vd,_vj));})));});return B(_mT(new T1(1,B(_nR(_qU,_qW,_vv))),_vC));});return new F(function(){return _mT(new T1(0,function(_w5){switch(E(_w5)){case 34:return E(_vt);case 39:return E(_vs);case 92:return E(_vr);case 97:return E(_vk);case 98:return E(_vl);case 102:return E(_vp);case 110:return E(_vn);case 114:return E(_vq);case 116:return E(_vm);case 118:return E(_vo);default:return new T0(2);}}),_vu);});},_w6=function(_w7){return new F(function(){return A1(_w7,_7f);});},_w8=function(_w9){var _wa=E(_w9);if(!_wa._){return E(_w6);}else{var _wb=E(_wa.a),_wc=_wb>>>0,_wd=new T(function(){return B(_w8(_wa.b));});if(_wc>887){var _we=u_iswspace(_wb);if(!E(_we)){return E(_w6);}else{var _wf=function(_wg){var _wh=new T(function(){return B(A1(_wd,_wg));});return new T1(0,function(_wi){return E(_wh);});};return E(_wf);}}else{var _wj=E(_wc);if(_wj==32){var _wk=function(_wl){var _wm=new T(function(){return B(A1(_wd,_wl));});return new T1(0,function(_wn){return E(_wm);});};return E(_wk);}else{if(_wj-9>>>0>4){if(E(_wj)==160){var _wo=function(_wp){var _wq=new T(function(){return B(A1(_wd,_wp));});return new T1(0,function(_wr){return E(_wq);});};return E(_wo);}else{return E(_w6);}}else{var _ws=function(_wt){var _wu=new T(function(){return B(A1(_wd,_wt));});return new T1(0,function(_wv){return E(_wu);});};return E(_ws);}}}}},_ww=function(_wx){var _wy=new T(function(){return B(_ww(_wx));}),_wz=function(_wA){return (E(_wA)==92)?E(_wy):new T0(2);},_wB=function(_wC){return E(new T1(0,_wz));},_wD=new T1(1,function(_wE){return new F(function(){return A2(_w8,_wE,_wB);});}),_wF=new T(function(){return B(_vi(function(_wG){return new F(function(){return A1(_wx,new T2(0,_wG,_kr));});}));}),_wH=function(_wI){var _wJ=E(_wI);if(_wJ==38){return E(_wy);}else{var _wK=_wJ>>>0;if(_wK>887){var _wL=u_iswspace(_wJ);return (E(_wL)==0)?new T0(2):E(_wD);}else{var _wM=E(_wK);return (_wM==32)?E(_wD):(_wM-9>>>0>4)?(E(_wM)==160)?E(_wD):new T0(2):E(_wD);}}};return new F(function(){return _mT(new T1(0,function(_wN){return (E(_wN)==92)?E(new T1(0,_wH)):new T0(2);}),new T1(0,function(_wO){var _wP=E(_wO);if(E(_wP)==92){return E(_wF);}else{return new F(function(){return A1(_wx,new T2(0,_wP,_qO));});}}));});},_wQ=function(_wR,_wS){var _wT=new T(function(){return B(A1(_wS,new T1(1,new T(function(){return B(A1(_wR,_10));}))));}),_wU=function(_wV){var _wW=E(_wV),_wX=E(_wW.a);if(E(_wX)==34){if(!E(_wW.b)){return E(_wT);}else{return new F(function(){return _wQ(function(_wY){return new F(function(){return A1(_wR,new T2(1,_wX,_wY));});},_wS);});}}else{return new F(function(){return _wQ(function(_wZ){return new F(function(){return A1(_wR,new T2(1,_wX,_wZ));});},_wS);});}};return new F(function(){return _ww(_wU);});},_x0=new T(function(){return B(unCStr("_\'"));}),_x1=function(_x2){var _x3=u_iswalnum(_x2);if(!E(_x3)){return new F(function(){return _4B(_6f,_x2,_x0);});}else{return true;}},_x4=function(_x5){return new F(function(){return _x1(E(_x5));});},_x6=new T(function(){return B(unCStr(",;()[]{}`"));}),_x7=new T(function(){return B(unCStr("=>"));}),_x8=new T2(1,_x7,_10),_x9=new T(function(){return B(unCStr("~"));}),_xa=new T2(1,_x9,_x8),_xb=new T(function(){return B(unCStr("@"));}),_xc=new T2(1,_xb,_xa),_xd=new T(function(){return B(unCStr("->"));}),_xe=new T2(1,_xd,_xc),_xf=new T(function(){return B(unCStr("<-"));}),_xg=new T2(1,_xf,_xe),_xh=new T(function(){return B(unCStr("|"));}),_xi=new T2(1,_xh,_xg),_xj=new T(function(){return B(unCStr("\\"));}),_xk=new T2(1,_xj,_xi),_xl=new T(function(){return B(unCStr("="));}),_xm=new T2(1,_xl,_xk),_xn=new T(function(){return B(unCStr("::"));}),_xo=new T2(1,_xn,_xm),_xp=new T(function(){return B(unCStr(".."));}),_xq=new T2(1,_xp,_xo),_xr=function(_xs){var _xt=new T(function(){return B(A1(_xs,_ov));}),_xu=new T(function(){var _xv=new T(function(){var _xw=function(_xx){var _xy=new T(function(){return B(A1(_xs,new T1(0,_xx)));});return new T1(0,function(_xz){return (E(_xz)==39)?E(_xy):new T0(2);});};return B(_vi(_xw));}),_xA=function(_xB){var _xC=E(_xB);switch(E(_xC)){case 39:return new T0(2);case 92:return E(_xv);default:var _xD=new T(function(){return B(A1(_xs,new T1(0,_xC)));});return new T1(0,function(_xE){return (E(_xE)==39)?E(_xD):new T0(2);});}},_xF=new T(function(){var _xG=new T(function(){return B(_wQ(_5V,_xs));}),_xH=new T(function(){var _xI=new T(function(){var _xJ=new T(function(){var _xK=function(_xL){var _xM=E(_xL),_xN=u_iswalpha(_xM);return (E(_xN)==0)?(E(_xM)==95)?new T1(1,B(_oh(_x4,function(_xO){return new F(function(){return A1(_xs,new T1(3,new T2(1,_xM,_xO)));});}))):new T0(2):new T1(1,B(_oh(_x4,function(_xP){return new F(function(){return A1(_xs,new T1(3,new T2(1,_xM,_xP)));});})));};return B(_mT(new T1(0,_xK),new T(function(){return new T1(1,B(_nR(_pt,_qJ,_xs)));})));}),_xQ=function(_xR){return (!B(_4B(_6f,_xR,_qL)))?new T0(2):new T1(1,B(_oh(_qM,function(_xS){var _xT=new T2(1,_xR,_xS);if(!B(_4B(_fq,_xT,_xq))){return new F(function(){return A1(_xs,new T1(4,_xT));});}else{return new F(function(){return A1(_xs,new T1(2,_xT));});}})));};return B(_mT(new T1(0,_xQ),_xJ));});return B(_mT(new T1(0,function(_xU){if(!B(_4B(_6f,_xU,_x6))){return new T0(2);}else{return new F(function(){return A1(_xs,new T1(2,new T2(1,_xU,_10)));});}}),_xI));});return B(_mT(new T1(0,function(_xV){return (E(_xV)==34)?E(_xG):new T0(2);}),_xH));});return B(_mT(new T1(0,function(_xW){return (E(_xW)==39)?E(new T1(0,_xA)):new T0(2);}),_xF));});return new F(function(){return _mT(new T1(1,function(_xX){return (E(_xX)._==0)?E(_xt):new T0(2);}),_xu);});},_xY=0,_xZ=function(_y0,_y1){var _y2=new T(function(){var _y3=new T(function(){var _y4=function(_y5){var _y6=new T(function(){var _y7=new T(function(){return B(A1(_y1,_y5));});return B(_xr(function(_y8){var _y9=E(_y8);return (_y9._==2)?(!B(_hb(_y9.a,_nw)))?new T0(2):E(_y7):new T0(2);}));}),_ya=function(_yb){return E(_y6);};return new T1(1,function(_yc){return new F(function(){return A2(_w8,_yc,_ya);});});};return B(A2(_y0,_xY,_y4));});return B(_xr(function(_yd){var _ye=E(_yd);return (_ye._==2)?(!B(_hb(_ye.a,_nv)))?new T0(2):E(_y3):new T0(2);}));}),_yf=function(_yg){return E(_y2);};return function(_yh){return new F(function(){return A2(_w8,_yh,_yf);});};},_yi=function(_yj,_yk){var _yl=function(_ym){var _yn=new T(function(){return B(A1(_yj,_ym));}),_yo=function(_yp){return new F(function(){return _mT(B(A1(_yn,_yp)),new T(function(){return new T1(1,B(_xZ(_yl,_yp)));}));});};return E(_yo);},_yq=new T(function(){return B(A1(_yj,_yk));}),_yr=function(_ys){return new F(function(){return _mT(B(A1(_yq,_ys)),new T(function(){return new T1(1,B(_xZ(_yl,_ys)));}));});};return E(_yr);},_yt=function(_yu,_yv){var _yw=function(_yx,_yy){var _yz=function(_yA){return new F(function(){return A1(_yy,new T(function(){return  -E(_yA);}));});},_yB=new T(function(){return B(_xr(function(_yC){return new F(function(){return A3(_yu,_yC,_yx,_yz);});}));}),_yD=function(_yE){return E(_yB);},_yF=function(_yG){return new F(function(){return A2(_w8,_yG,_yD);});},_yH=new T(function(){return B(_xr(function(_yI){var _yJ=E(_yI);if(_yJ._==4){var _yK=E(_yJ.a);if(!_yK._){return new F(function(){return A3(_yu,_yJ,_yx,_yy);});}else{if(E(_yK.a)==45){if(!E(_yK.b)._){return E(new T1(1,_yF));}else{return new F(function(){return A3(_yu,_yJ,_yx,_yy);});}}else{return new F(function(){return A3(_yu,_yJ,_yx,_yy);});}}}else{return new F(function(){return A3(_yu,_yJ,_yx,_yy);});}}));}),_yL=function(_yM){return E(_yH);};return new T1(1,function(_yN){return new F(function(){return A2(_w8,_yN,_yL);});});};return new F(function(){return _yi(_yw,_yv);});},_yO=function(_yP){var _yQ=E(_yP);if(!_yQ._){var _yR=_yQ.b,_yS=new T(function(){return B(_pV(new T(function(){return B(_pB(E(_yQ.a)));}),new T(function(){return B(_7a(_yR,0));},1),B(_j4(_pD,_yR))));});return new T1(1,_yS);}else{return (E(_yQ.b)._==0)?(E(_yQ.c)._==0)?new T1(1,new T(function(){return B(_qc(_pA,_yQ.a));})):__Z:__Z;}},_yT=function(_yU,_yV){return new T0(2);},_yW=function(_yX){var _yY=E(_yX);if(_yY._==5){var _yZ=B(_yO(_yY.a));if(!_yZ._){return E(_yT);}else{var _z0=new T(function(){return B(_8n(_yZ.a));});return function(_z1,_z2){return new F(function(){return A1(_z2,_z0);});};}}else{return E(_yT);}},_z3=function(_z4){var _z5=function(_z6){return E(new T2(3,_z4,_nI));};return new T1(1,function(_z7){return new F(function(){return A2(_w8,_z7,_z5);});});},_z8=new T(function(){return B(A3(_yt,_yW,_xY,_z3));}),_z9=new T(function(){return B(_a2("Event.hs:(27,1)-(33,83)|function putCell"));}),_za=function(_zb){while(1){var _zc=B((function(_zd){var _ze=E(_zd);if(!_ze._){return __Z;}else{var _zf=_ze.b,_zg=E(_ze.a);if(!E(_zg.b)._){return new T2(1,_zg.a,new T(function(){return B(_za(_zf));}));}else{_zb=_zf;return __continue;}}})(_zb));if(_zc!=__continue){return _zc;}}},_zh=function(_zi,_zj,_zk,_zl,_zm,_zn,_zo,_zp,_zq,_zr,_zs,_zt,_zu,_zv,_zw,_zx,_zy,_zz,_zA,_zB,_zC,_zD,_zE){while(1){var _zF=B((function(_zG,_zH,_zI,_zJ,_zK,_zL,_zM,_zN,_zO,_zP,_zQ,_zR,_zS,_zT,_zU,_zV,_zW,_zX,_zY,_zZ,_A0,_A1,_A2){var _A3=E(_zG);if(!_A3._){return {_:0,a:_zH,b:_zI,c:_zJ,d:_zK,e:_zL,f:_zM,g:_zN,h:_zO,i:_zP,j:_zQ,k:_zR,l:_zS,m:_zT,n:_zU,o:_zV,p:_zW,q:_zX,r:_zY,s:_zZ,t:_A0,u:_A1,v:_A2};}else{var _A4=E(_A3.b);if(!_A4._){return E(_z9);}else{var _A5=E(_zH),_A6=new T(function(){var _A7=E(_A3.a);if(!_A7._){return E(_mE);}else{var _A8=E(_A7.b);if(!_A8._){return E(_mE);}else{var _A9=_A8.a,_Aa=_A8.b,_Ab=E(_A7.a);if(E(_Ab)==44){return new T2(0,_10,new T(function(){return E(B(_ky(44,_A9,_Aa)).a);}));}else{var _Ac=B(_ky(44,_A9,_Aa)),_Ad=E(_Ac.b);if(!_Ad._){return E(_mE);}else{return new T2(0,new T2(1,_Ab,_Ac.a),_Ad.a);}}}}}),_Ae=B(_za(B(_mJ(_z8,new T(function(){return E(E(_A6).b);})))));if(!_Ae._){return E(_mz);}else{if(!E(_Ae.b)._){var _Af=new T(function(){var _Ag=E(_A4.a);if(!_Ag._){return E(_mH);}else{var _Ah=E(_Ag.b);if(!_Ah._){return E(_mH);}else{var _Ai=_Ah.a,_Aj=_Ah.b,_Ak=E(_Ag.a);if(E(_Ak)==44){return new T2(0,_10,new T(function(){return E(B(_ky(44,_Ai,_Aj)).a);}));}else{var _Al=B(_ky(44,_Ai,_Aj)),_Am=E(_Al.b);if(!_Am._){return E(_mH);}else{return new T2(0,new T2(1,_Ak,_Al.a),_Am.a);}}}}}),_An=new T(function(){var _Ao=B(_za(B(_mJ(_z8,new T(function(){return E(E(_A6).a);})))));if(!_Ao._){return E(_mz);}else{if(!E(_Ao.b)._){return E(_Ao.a);}else{return E(_mB);}}},1),_Ap=_zI,_Aq=_zJ,_Ar=_zK,_As=_zL,_At=_zM,_Au=_zN,_Av=_zO,_Aw=_zP,_Ax=_zQ,_Ay=_zR,_Az=_zS,_AA=_zT,_AB=_zU,_AC=_zV,_AD=_zW,_AE=_zX,_AF=_zY,_AG=_zZ,_AH=_A0,_AI=_A1,_AJ=_A2;_zi=_A4.b;_zj={_:0,a:E(_A5.a),b:E(B(_m9(_An,E(_Ae.a),new T(function(){return B(_h7(E(_Af).a));}),new T(function(){return B(_hq(E(_Af).b));}),_A5.b))),c:_A5.c,d:_A5.d,e:_A5.e,f:_A5.f,g:E(_A5.g),h:E(_A5.h),i:E(_A5.i)};_zk=_Ap;_zl=_Aq;_zm=_Ar;_zn=_As;_zo=_At;_zp=_Au;_zq=_Av;_zr=_Aw;_zs=_Ax;_zt=_Ay;_zu=_Az;_zv=_AA;_zw=_AB;_zx=_AC;_zy=_AD;_zz=_AE;_zA=_AF;_zB=_AG;_zC=_AH;_zD=_AI;_zE=_AJ;return __continue;}else{return E(_mB);}}}}})(_zi,_zj,_zk,_zl,_zm,_zn,_zo,_zp,_zq,_zr,_zs,_zt,_zu,_zv,_zw,_zx,_zy,_zz,_zA,_zB,_zC,_zD,_zE));if(_zF!=__continue){return _zF;}}},_AK=function(_AL){var _AM=E(_AL);if(!_AM._){return new T2(0,_10,_10);}else{var _AN=E(_AM.a),_AO=new T(function(){var _AP=B(_AK(_AM.b));return new T2(0,_AP.a,_AP.b);});return new T2(0,new T2(1,_AN.a,new T(function(){return E(E(_AO).a);})),new T2(1,_AN.b,new T(function(){return E(E(_AO).b);})));}},_AQ=0,_AR=0,_AS=32,_AT=function(_AU,_AV,_AW,_AX){var _AY=E(_AX);if(!_AY._){return __Z;}else{var _AZ=_AY.b;if(!B(_4B(_3M,_AU,_AW))){var _B0=new T(function(){return B(_AT(new T(function(){return E(_AU)+1|0;}),_AV,_AW,_AZ));});return new T2(1,_AY.a,_B0);}else{var _B1=new T(function(){return B(_AT(new T(function(){return E(_AU)+1|0;}),_AV,_AW,_AZ));});return new T2(1,_AV,_B1);}}},_B2=function(_B3,_B4){var _B5=E(_B4);if(!_B5._){return __Z;}else{var _B6=new T(function(){var _B7=B(_AK(_B5.a)),_B8=_B7.a,_B9=new T(function(){return B(_gF(0,_B3,_B8));});return B(_gT(B(_AT(_AR,_AS,_B9,_B8)),new T(function(){return B(_gM(0,_AQ,_B9,_B7.b));},1)));});return new T2(1,_B6,new T(function(){return B(_B2(_B3,_B5.b));}));}},_Ba=function(_Bb,_Bc){var _Bd=E(_Bc);return (_Bd._==0)?__Z:new T2(1,_Bb,new T(function(){return B(_Ba(_Bd.a,_Bd.b));}));},_Be=new T(function(){return B(unCStr("init"));}),_Bf=new T(function(){return B(_dG(_Be));}),_Bg=function(_Bh,_Bi){var _Bj=function(_Bk){var _Bl=E(_Bk);if(!_Bl._){return __Z;}else{var _Bm=new T(function(){return B(_y(new T2(1,_Bh,_10),new T(function(){return B(_Bj(_Bl.b));},1)));},1);return new F(function(){return _y(_Bl.a,_Bm);});}},_Bn=B(_Bj(_Bi));if(!_Bn._){return E(_Bf);}else{return new F(function(){return _Ba(_Bn.a,_Bn.b);});}},_Bo=61,_Bp=46,_Bq=new T(function(){return B(_a2("Event.hs:(70,1)-(76,61)|function makeDecision"));}),_Br=new T(function(){return B(unCStr("if"));}),_Bs=new T(function(){return B(unCStr("ch"));}),_Bt=new T(function(){return B(unCStr("cleq"));}),_Bu=new T(function(){return B(unCStr("da"));}),_Bv=new T(function(){return B(unCStr("ct"));}),_Bw=function(_Bx,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT){var _BU=function(_BV,_BW){var _BX=function(_BY){if(!B(_hb(_BV,_Bv))){if(!B(_hb(_BV,_Bu))){var _BZ=function(_C0){if(!B(_hb(_BV,_Bt))){var _C1=function(_C2){if(!B(_hb(_BV,_Bs))){if(!B(_hb(_BV,_Br))){return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}else{var _C3=E(_BW);if(!_C3._){return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}else{var _C4=_C3.a,_C5=E(_C3.b);if(!_C5._){return E(_Bq);}else{var _C6=_C5.a,_C7=B(_kl(_BD)),_C8=_C7.a,_C9=_C7.b,_Ca=function(_Cb){if(!B(_4B(_fq,_C4,_C8))){return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}else{if(!B(_hb(_C6,B(_77(_C9,B(_iC(_fq,_C4,_C8))))))){return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}else{return new F(function(){return _Bw(_Cb,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}}},_Cc=B(_Bg(_Bp,_C5.b));if(!_Cc._){return new F(function(){return _Ca(_10);});}else{var _Cd=_Cc.a,_Ce=E(_Cc.b);if(!_Ce._){return new F(function(){return _Ca(new T2(1,_Cd,_10));});}else{var _Cf=_Ce.a,_Cg=_Ce.b,_Ch=E(_Cd);if(E(_Ch)==47){if(!B(_4B(_fq,_C4,_C8))){return new F(function(){return _Bw(B(_ky(47,_Cf,_Cg)).a,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}else{if(!B(_hb(_C6,B(_77(_C9,B(_iC(_fq,_C4,_C8))))))){return new F(function(){return _Bw(B(_ky(47,_Cf,_Cg)).a,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}else{return new F(function(){return _Bw(_10,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}}}else{if(!B(_4B(_fq,_C4,_C8))){var _Ci=E(B(_ky(47,_Cf,_Cg)).b);if(!_Ci._){return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}else{return new F(function(){return _Bw(_Ci.a,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}}else{if(!B(_hb(_C6,B(_77(_C9,B(_iC(_fq,_C4,_C8))))))){var _Cj=E(B(_ky(47,_Cf,_Cg)).b);if(!_Cj._){return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}else{return new F(function(){return _Bw(_Cj.a,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}}else{return new F(function(){return _Bw(new T2(1,_Ch,new T(function(){return E(B(_ky(47,_Cf,_Cg)).a);})),_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}}}}}}}}}else{return new F(function(){return _kG(_BW,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT);});}},_Ck=E(_BV);if(!_Ck._){return new F(function(){return _C1(_);});}else{if(E(_Ck.a)==109){if(!E(_Ck.b)._){var _Cl=B(_fW(_BW,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT));return {_:0,a:E(_Cl.a),b:E(_Cl.b),c:E(_Cl.c),d:E(_Cl.d),e:E(_Cl.e),f:E(_Cl.f),g:E(_Cl.g),h:_Cl.h,i:_Cl.i,j:_Cl.j,k:_Cl.k,l:E(_Cl.l),m:_Cl.m,n:E(_Cl.n),o:E(_Cl.o),p:E(_Cl.p),q:E(_Cl.q),r:E(_Cl.r),s:E(_Cl.s),t:E(_Cl.t),u:E(_Cl.u),v:_Cl.v};}else{return new F(function(){return _C1(_);});}}else{return new F(function(){return _C1(_);});}}}else{var _Cm=E(_By);return {_:0,a:E({_:0,a:E(_Cm.a),b:E(B(_B2(_Bo,_Cm.b))),c:_Cm.c,d:_Cm.d,e:_Cm.e,f:_Cm.f,g:E(_Cm.g),h:E(_Cm.h),i:E(_Cm.i)}),b:E(_Bz),c:E(_BA),d:E(_BB),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}},_Cn=E(_BV);if(!_Cn._){return new F(function(){return _BZ(_);});}else{if(E(_Cn.a)==112){if(!E(_Cn.b)._){var _Co=B(_zh(_BW,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT));return {_:0,a:E(_Co.a),b:E(_Co.b),c:E(_Co.c),d:E(_Co.d),e:E(_Co.e),f:E(_Co.f),g:E(_Co.g),h:_Co.h,i:_Co.i,j:_Co.j,k:_Co.k,l:E(_Co.l),m:_Co.m,n:E(_Co.n),o:E(_Co.o),p:E(_Co.p),q:E(_Co.q),r:E(_Co.r),s:E(_Co.s),t:E(_Co.t),u:E(_Co.u),v:_Co.v};}else{return new F(function(){return _BZ(_);});}}else{return new F(function(){return _BZ(_);});}}}else{return {_:0,a:E(_By),b:E(_Bz),c:E(_BA),d:E(_10),e:E(_BC),f:E(_BD),g:E(_BE),h:_BF,i:_BG,j:_BH,k:_BI,l:E(_BJ),m:_BK,n:E(_BL),o:E(_BM),p:E(_BN),q:E(_BO),r:E(_BP),s:E(_BQ),t:E(_BR),u:E(_BS),v:_BT};}}else{var _Cp=B(_hs(_BW,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT));return {_:0,a:E(_Cp.a),b:E(_Cp.b),c:E(_Cp.c),d:E(_Cp.d),e:E(_Cp.e),f:E(_Cp.f),g:E(_Cp.g),h:_Cp.h,i:_Cp.i,j:_Cp.j,k:_Cp.k,l:E(_Cp.l),m:_Cp.m,n:E(_Cp.n),o:E(_Cp.o),p:E(_Cp.p),q:E(_Cp.q),r:E(_Cp.r),s:E(_Cp.s),t:E(_Cp.t),u:E(_Cp.u),v:_Cp.v};}},_Cq=E(_BV);if(!_Cq._){return new F(function(){return _BX(_);});}else{var _Cr=_Cq.b;switch(E(_Cq.a)){case 100:if(!E(_Cr)._){var _Cs=B(_j8(_BW,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT));return {_:0,a:E(_Cs.a),b:E(_Cs.b),c:E(_Cs.c),d:E(_Cs.d),e:E(_Cs.e),f:E(_Cs.f),g:E(_Cs.g),h:_Cs.h,i:_Cs.i,j:_Cs.j,k:_Cs.k,l:E(_Cs.l),m:_Cs.m,n:E(_Cs.n),o:E(_Cs.o),p:E(_Cs.p),q:E(_Cs.q),r:E(_Cs.r),s:E(_Cs.s),t:E(_Cs.t),u:E(_Cs.u),v:_Cs.v};}else{return new F(function(){return _BX(_);});}break;case 101:if(!E(_Cr)._){var _Ct=B(_ft(_BW,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT));return {_:0,a:E(_Ct.a),b:E(_Ct.b),c:E(_Ct.c),d:E(_Ct.d),e:E(_Ct.e),f:E(_Ct.f),g:E(_Ct.g),h:_Ct.h,i:_Ct.i,j:_Ct.j,k:_Ct.k,l:E(_Ct.l),m:_Ct.m,n:E(_Ct.n),o:E(_Ct.o),p:E(_Ct.p),q:E(_Ct.q),r:E(_Ct.r),s:E(_Ct.s),t:E(_Ct.t),u:E(_Ct.u),v:_Ct.v};}else{return new F(function(){return _BX(_);});}break;default:return new F(function(){return _BX(_);});}}},_Cu=E(_Bx);if(!_Cu._){return new F(function(){return _BU(_10,_10);});}else{var _Cv=_Cu.a,_Cw=E(_Cu.b);if(!_Cw._){return new F(function(){return _BU(new T2(1,_Cv,_10),_10);});}else{var _Cx=E(_Cv),_Cy=new T(function(){var _Cz=B(_ky(46,_Cw.a,_Cw.b));return new T2(0,_Cz.a,_Cz.b);});if(E(_Cx)==46){return new F(function(){return _BU(_10,new T2(1,new T(function(){return E(E(_Cy).a);}),new T(function(){return E(E(_Cy).b);})));});}else{return new F(function(){return _BU(new T2(1,_Cx,new T(function(){return E(E(_Cy).a);})),new T(function(){return E(E(_Cy).b);}));});}}}},_CA=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_CB=new T(function(){return eval("(function(ctx){ctx.save();})");}),_CC=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_CD=function(_CE,_CF,_CG,_){var _CH=__app1(E(_CB),_CG),_CI=__app2(E(_CC),_CG,E(_CE)),_CJ=B(A2(_CF,_CG,_)),_CK=__app1(E(_CA),_CG);return new F(function(){return _7g(_);});},_CL=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_CM=function(_CN,_CO,_CP,_CQ,_){var _CR=__app1(E(_CB),_CQ),_CS=__app3(E(_CL),_CQ,E(_CN),E(_CO)),_CT=B(A2(_CP,_CQ,_)),_CU=__app1(E(_CA),_CQ);return new F(function(){return _7g(_);});},_CV=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e"));}),_CW=function(_CX){if(_CX<=31){return new F(function(){return _4B(_6f,_CX,_CV);});}else{if(_CX>=128){return new F(function(){return _4B(_6f,_CX,_CV);});}else{return true;}}},_CY=1.5707963267948966,_CZ=new T(function(){return B(unCStr("px VL Gothic"));}),_D0=function(_D1,_D2,_D3,_D4,_D5,_D6,_D7){var _D8=new T(function(){var _D9=new T(function(){if(E(_D3)==8){return new T2(0,new T(function(){return E(_D5)*28+20;}),new T(function(){return E(_D6)*20+8*(E(_D4)-1);}));}else{return new T2(0,new T(function(){return E(_D5)*28;}),new T(function(){return E(_D6)*20;}));}}),_Da=new T(function(){return B(_CW(E(_D7)));}),_Db=new T(function(){var _Dc=E(E(_D9).a);if(!E(_Da)){return E(_Dc);}else{return _Dc+3.3333333333333335;}}),_Dd=new T(function(){var _De=E(E(_D9).b);if(!E(_Da)){return E(_De);}else{return _De-16.666666666666668;}}),_Df=new T(function(){if(!E(_Da)){return E(_cl);}else{return E(_CY);}}),_Dg=new T(function(){return B(_7i(_cl,_cl,new T2(1,_D7,_10)));}),_Dh=function(_Di,_){return new F(function(){return _CD(_Df,_Dg,E(_Di),_);});};return B(_d3(new T(function(){return B(_y(B(_I(0,E(_D3),_10)),_CZ));},1),function(_Dj,_){return new F(function(){return _CM(_Db,_Dd,_Dh,E(_Dj),_);});}));});return new F(function(){return A3(_cI,_D2,_D8,_D1);});},_Dk=15,_Dl=new T(function(){return B(unCStr("last"));}),_Dm=new T(function(){return B(_dG(_Dl));}),_Dn=27,_Do=1,_Dp=65306,_Dq=125,_Dr=function(_Ds){return E(E(_Ds).b);},_Dt=function(_Du,_Dv,_Dw){var _Dx=E(_Dv),_Dy=E(_Dw),_Dz=new T(function(){var _DA=B(_c8(_Du)),_DB=B(_Dt(_Du,_Dy,B(A3(_Dr,_DA,new T(function(){return B(A3(_ca,_DA,_Dy,_Dy));}),_Dx))));return new T2(1,_DB.a,_DB.b);});return new T2(0,_Dx,_Dz);},_DC=1,_DD=new T(function(){var _DE=B(_Dt(_c6,_cl,_DC));return new T2(1,_DE.a,_DE.b);}),_DF=42,_DG=function(_DH,_DI,_DJ){var _DK=E(_DH);if(!_DK._){return __Z;}else{var _DL=_DK.a,_DM=_DK.b;if(_DI!=_DJ){var _DN=E(_DL);return (_DN._==0)?E(_dJ):(E(_DN.a)==42)?new T2(1,new T2(1,_dN,_DN.b),new T(function(){return B(_DG(_DM,_DI,_DJ+1|0));})):new T2(1,new T2(1,_dN,_DN),new T(function(){return B(_DG(_DM,_DI,_DJ+1|0));}));}else{var _DO=E(_DL);return (_DO._==0)?E(_dJ):(E(_DO.a)==42)?new T2(1,new T2(1,_dN,_DO),new T(function(){return B(_DG(_DM,_DI,_DJ+1|0));})):new T2(1,new T2(1,_DF,_DO),new T(function(){return B(_DG(_DM,_DI,_DJ+1|0));}));}}},_DP=function(_DQ,_DR,_DS){var _DT=E(_DQ);if(!_DT._){return __Z;}else{var _DU=_DT.a,_DV=_DT.b,_DW=E(_DR);if(_DW!=_DS){var _DX=E(_DU);return (_DX._==0)?E(_dJ):(E(_DX.a)==42)?new T2(1,new T2(1,_dN,_DX.b),new T(function(){return B(_DG(_DV,_DW,_DS+1|0));})):new T2(1,new T2(1,_dN,_DX),new T(function(){return B(_DG(_DV,_DW,_DS+1|0));}));}else{var _DY=E(_DU);return (_DY._==0)?E(_dJ):(E(_DY.a)==42)?new T2(1,new T2(1,_dN,_DY),new T(function(){return B(_DG(_DV,_DW,_DS+1|0));})):new T2(1,new T2(1,_DF,_DY),new T(function(){return B(_DG(_DV,_DW,_DS+1|0));}));}}},_DZ=new T(function(){return B(unCStr("\n\n"));}),_E0=function(_E1){var _E2=E(_E1);if(!_E2._){return __Z;}else{var _E3=new T(function(){return B(_y(_DZ,new T(function(){return B(_E0(_E2.b));},1)));},1);return new F(function(){return _y(_E2.a,_E3);});}},_E4=function(_E5,_E6,_E7){var _E8=new T(function(){return B(unAppCStr("\n\n",new T(function(){return B(_E0(B(_DP(_E6,_E7,0))));})));},1);return new F(function(){return _y(_E5,_E8);});},_E9=20,_Ea=64,_Eb=3,_Ec=0,_Ed=function(_Ee,_Ef,_Eg,_Eh,_Ei,_Ej,_){while(1){var _Ek=B((function(_El,_Em,_En,_Eo,_Ep,_Eq,_){var _Er=E(_Eq);if(!_Er._){return _7f;}else{var _Es=_Er.b;if(E(_Er.a)==125){var _Et=new T(function(){var _Eu=E(_Ep);if((_Eu+1)*20<=557){return new T2(0,_Eo,_Eu+1|0);}else{return new T2(0,new T(function(){return E(_Eo)-1|0;}),_En);}});return new F(function(){return _Ev(_El,_Em,_En,new T(function(){return E(E(_Et).a);}),new T(function(){return E(E(_Et).b);}),_Es,_);});}else{var _Ew=_El,_Ex=_Em,_Ey=_En,_Ez=_Eo,_EA=_Ep;_Ee=_Ew;_Ef=_Ex;_Eg=_Ey;_Eh=_Ez;_Ei=_EA;_Ej=_Es;return __continue;}}})(_Ee,_Ef,_Eg,_Eh,_Ei,_Ej,_));if(_Ek!=__continue){return _Ek;}}},_Ev=function(_EB,_EC,_ED,_EE,_EF,_EG,_){while(1){var _EH=B((function(_EI,_EJ,_EK,_EL,_EM,_EN,_){var _EO=E(_EN);if(!_EO._){return _7f;}else{var _EP=_EO.b,_EQ=E(_EO.a),_ER=E(_EQ);switch(_ER){case 10:var _ES=_EI,_ET=_EK,_EU=_EK;_EB=_ES;_EC=_Ec;_ED=_ET;_EE=new T(function(){return E(_EL)-1|0;});_EF=_EU;_EG=_EP;return __continue;case 123:return new F(function(){return _Ed(_EI,_EJ,_EK,_EL,_EM,_EP,_);});break;case 65306:return new F(function(){return A(_EV,[_EI,_EJ,_EK,new T(function(){if(E(_EK)!=E(_EM)){return E(_EL);}else{return E(_EL)+1|0;}}),new T(function(){var _EW=E(_EM);if(E(_EK)!=_EW){return _EW-1|0;}else{return E(_Dn);}}),_EP,_]);});break;default:var _EX=function(_EY,_EZ){var _F0=new T(function(){switch(E(_ER)){case 42:return E(_Eb);break;case 12300:return E(_Do);break;default:return E(_EJ);}}),_F1=function(_){var _F2=new T(function(){var _F3=E(_EM);if((_F3+1)*20<=557){return new T2(0,_EL,_F3+1|0);}else{return new T2(0,new T(function(){return E(_EL)-1|0;}),_EK);}});return new F(function(){return _Ev(_EI,_F0,_EK,new T(function(){return E(E(_F2).a);}),new T(function(){return E(E(_F2).b);}),_EP,_);});};if(E(_EY)==64){return new F(function(){return _F1(_);});}else{var _F4=B(A(_D0,[E(_EI).a,new T(function(){return B(_77(_em,E(_F0)));},1),_E9,_cl,_EL,_EM,_EZ,_]));return new F(function(){return _F1(_);});}},_F5=E(_ER);switch(_F5){case 42:return new F(function(){return _EX(64,_Ea);});break;case 12289:return new F(function(){return _EX(64,_Ea);});break;case 12290:return new F(function(){return _EX(64,_Ea);});break;default:return new F(function(){return _EX(_F5,_EQ);});}}}})(_EB,_EC,_ED,_EE,_EF,_EG,_));if(_EH!=__continue){return _EH;}}},_F6=8,_EV=function(_F7,_F8,_F9,_Fa,_Fb){var _Fc=new T(function(){return B(_77(_em,E(_F8)));}),_Fd=function(_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_){while(1){var _Fl=B((function(_Fm,_Fn,_Fo,_Fp,_Fq,_Fr,_Fs,_){var _Ft=E(_Fs);if(!_Ft._){return _7f;}else{var _Fu=_Ft.b,_Fv=E(_Ft.a);if(E(_Fv)==65306){var _Fw=new T(function(){var _Fx=E(_Fr);if((_Fx+1)*20<=557){return new T2(0,_Fq,_Fx+1|0);}else{return new T2(0,new T(function(){return E(_Fq)-1|0;}),_Fo);}});return new F(function(){return _Fy(_Fm,_Fn,_F8,_Fo,new T(function(){return E(E(_Fw).a);}),new T(function(){return E(E(_Fw).b);}),_Fu,_);});}else{var _Fz=B(A(_D0,[_Fm,_Fc,_F6,_Fp,_Fq,_Fr,_Fv,_])),_FA=_Fm,_FB=_Fn,_FC=_Fo,_FD=_Fq,_FE=_Fr;_Fe=_FA;_Ff=_FB;_Fg=_FC;_Fh=new T(function(){return E(_Fp)+1;});_Fi=_FD;_Fj=_FE;_Fk=_Fu;return __continue;}}})(_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_));if(_Fl!=__continue){return _Fl;}}},_FF=function(_FG,_){var _FH=E(_FG);if(!_FH._){return _7f;}else{var _FI=_FH.b,_FJ=E(_FH.a);if(E(_FJ)==65306){var _FK=new T(function(){var _FL=E(_Fb);if((_FL+1)*20<=557){return new T2(0,_Fa,_FL+1|0);}else{return new T2(0,new T(function(){return E(_Fa)-1|0;}),_F9);}});return new F(function(){return _Ev(_F7,_F8,_F9,new T(function(){return E(E(_FK).a);}),new T(function(){return E(E(_FK).b);}),_FI,_);});}else{var _FM=E(_F7),_FN=_FM.a,_FO=B(A(_D0,[_FN,_Fc,_F6,_cl,_Fa,_Fb,_FJ,_]));return new F(function(){return _Fd(_FN,_FM.b,_F9,1,_Fa,_Fb,_FI,_);});}}};return E(_FF);},_Fy=function(_FP,_FQ,_FR,_FS,_FT,_FU,_FV,_){while(1){var _FW=B((function(_FX,_FY,_FZ,_G0,_G1,_G2,_G3,_){var _G4=E(_G3);if(!_G4._){return _7f;}else{var _G5=_G4.b,_G6=E(_G4.a),_G7=E(_G6);switch(_G7){case 10:var _G8=_FX,_G9=_FY,_Ga=_G0,_Gb=_G0;_FP=_G8;_FQ=_G9;_FR=_Ec;_FS=_Ga;_FT=new T(function(){return E(_G1)-1|0;});_FU=_Gb;_FV=_G5;return __continue;case 123:return new F(function(){return _Ed(new T2(0,_FX,_FY),_FZ,_G0,_G1,_G2,_G5,_);});break;case 65306:return new F(function(){return A(_EV,[new T2(0,_FX,_FY),_FZ,_G0,new T(function(){if(E(_G0)!=E(_G2)){return E(_G1);}else{return E(_G1)+1|0;}}),new T(function(){var _Gc=E(_G2);if(E(_G0)!=_Gc){return _Gc-1|0;}else{return E(_Dn);}}),_G5,_]);});break;default:var _Gd=function(_Ge,_Gf){var _Gg=new T(function(){switch(E(_G7)){case 42:return E(_Eb);break;case 12300:return E(_Do);break;default:return E(_FZ);}}),_Gh=function(_){var _Gi=new T(function(){var _Gj=E(_G2);if((_Gj+1)*20<=557){return new T2(0,_G1,_Gj+1|0);}else{return new T2(0,new T(function(){return E(_G1)-1|0;}),_G0);}});return new F(function(){return _Fy(_FX,_FY,_Gg,_G0,new T(function(){return E(E(_Gi).a);}),new T(function(){return E(E(_Gi).b);}),_G5,_);});};if(E(_Ge)==64){return new F(function(){return _Gh(_);});}else{var _Gk=B(A(_D0,[_FX,new T(function(){return B(_77(_em,E(_Gg)));},1),_E9,_cl,_G1,_G2,_Gf,_]));return new F(function(){return _Gh(_);});}},_Gl=E(_G7);switch(_Gl){case 42:return new F(function(){return _Gd(64,_Ea);});break;case 12289:return new F(function(){return _Gd(64,_Ea);});break;case 12290:return new F(function(){return _Gd(64,_Ea);});break;default:return new F(function(){return _Gd(_Gl,_G6);});}}}})(_FP,_FQ,_FR,_FS,_FT,_FU,_FV,_));if(_FW!=__continue){return _FW;}}},_Gm=function(_Gn,_Go,_Gp,_Gq,_Gr,_Gs,_Gt,_Gu,_Gv,_Gw,_Gx,_Gy,_Gz,_GA,_GB,_GC,_GD,_GE,_GF,_GG,_GH,_GI,_GJ,_GK,_GL,_GM,_GN,_GO,_GP,_GQ,_GR,_GS,_GT,_){var _GU=new T2(0,_GD,_GE);if(!E(_GN)){return {_:0,a:E({_:0,a:E(_Go),b:E(_Gp),c:_Gq,d:_Gr,e:_Gs,f:_Gt,g:E(_Gu),h:E(_Gv),i:E(_Gw)}),b:E(new T2(0,_Gx,_Gy)),c:E(_Gz),d:E(_GA),e:E(_GB),f:E(_GC),g:E(_GU),h:_GF,i:_GG,j:_GH,k:_GI,l:E(_GJ),m:_GK,n:E(_GL),o:E(_GM),p:E(_qO),q:E(_GO),r:E(_GP),s:E(_GQ),t:E(_GR),u:E(_GS),v:_GT};}else{if(!E(_GO)){var _GV=_GF+1|0;if(0>=_GV){return E(_Dm);}else{var _GW=B(_f5(_Gz,_GV,_Dm)),_GX=function(_GY){if(E(_GY)==65306){var _GZ=true;}else{var _GZ=false;}var _H0=new T(function(){if(E(_GY)==10){return true;}else{return false;}}),_H1=new T(function(){if(!E(_H0)){if(E(_GY)==12300){return E(_Do);}else{return _GG;}}else{return E(_Ec);}}),_H2=new T(function(){return B(_77(_em,E(_H1)));}),_H3=new T(function(){return (2+E(_Gy)|0)+3|0;}),_H4=new T(function(){if(!E(_GF)){return new T2(0,_Dk,_H3);}else{return E(_GU);}}),_H5=new T(function(){return E(E(_H4).a);}),_H6=new T(function(){return E(E(_H4).b);}),_H7=new T(function(){if(!E(_GZ)){if(!E(_H0)){var _H8=E(_H6);if((_H8+1)*20<=557){return new T2(0,_H5,_H8+1|0);}else{return new T2(0,new T(function(){return E(_H5)-1|0;}),_H3);}}else{return new T2(0,new T(function(){return E(_H5)-1|0;}),_H3);}}else{return new T2(0,_H5,_H6);}}),_H9=new T(function(){if(E(E(_H7).a)==1){if(E(_H5)==1){return false;}else{return true;}}else{return false;}}),_Ha=new T(function(){if(!E(_GZ)){return __Z;}else{return B(_f0(_Dp,_GF,_Gz));}}),_Hb=new T(function(){if(E(_GY)==123){return true;}else{return false;}}),_Hc=new T(function(){if(!E(_Hb)){return __Z;}else{return B(_f0(_Dq,_GF,_Gz));}}),_Hd=new T(function(){if(!E(_Hb)){if(E(_GW)==12290){var _He=true;}else{var _He=false;}return {_:0,a:E({_:0,a:E(_Go),b:E(_Gp),c:_Gq,d:_Gr,e:_Gs,f:_Gt,g:E(_Gu),h:E(_Gv),i:E(_Gw)}),b:E(new T2(0,_Gx,_Gy)),c:E(_Gz),d:E(_GA),e:E(_GB),f:E(_GC),g:E(_GU),h:_GF,i:_GG,j:_GH,k:_GI,l:E(_GJ),m:_GK,n:E(_GL),o:E(_GM),p:E(_kr),q:E(_He),r:E(_GP),s:E(_GQ),t:E(_GR),u:E(_GS),v:_GT};}else{if(E(_GW)==12290){var _Hf=true;}else{var _Hf=false;}return B(_Bw(_Hc,{_:0,a:E(_Go),b:E(_Gp),c:_Gq,d:_Gr,e:_Gs,f:_Gt,g:E(_Gu),h:E(_Gv),i:E(_Gw)},new T2(0,_Gx,_Gy),_Gz,_GA,_GB,_GC,_GU,_GF,_GG,_GH,_GI,_GJ,_GK,_GL,_GM,_kr,_Hf,_GP,_GQ,_GR,_GS,_GT));}}),_Hg=new T(function(){if(!E(_GF)){return E(_Ec);}else{return E(_Hd).j;}}),_Hh=function(_){return new T(function(){var _Hi=E(_Hd),_Hj=_Hi.a,_Hk=_Hi.b,_Hl=_Hi.c,_Hm=_Hi.d,_Hn=_Hi.e,_Ho=_Hi.f,_Hp=_Hi.k,_Hq=_Hi.l,_Hr=_Hi.m,_Hs=_Hi.n,_Ht=_Hi.o,_Hu=_Hi.q,_Hv=_Hi.r,_Hw=_Hi.s,_Hx=_Hi.t,_Hy=_Hi.u,_Hz=_Hi.v;if(!E(_H9)){var _HA=E(_H7);}else{var _HA=new T2(0,_H5,_H3);}var _HB=function(_HC){var _HD=B(_7a(_Gz,0))-1|0;if((_GF+_HC|0)<=_HD){var _HE=E(_H1);return (!E(_H9))?{_:0,a:E(_Hj),b:E(_Hk),c:E(_Hl),d:E(_Hm),e:E(_Hn),f:E(_Ho),g:E(_HA),h:_GF+_HC|0,i:_HE,j:E(_Hg),k:_Hp,l:E(_Hq),m:_Hr,n:E(_Hs),o:E(_Ht),p:(_GF+_HC|0)<=_HD,q:E(_Hu),r:E(_Hv),s:E(_Hw),t:E(_Hx),u:E(_Hy),v:_Hz}:{_:0,a:E(_Hj),b:E(_Hk),c:E(_Hl),d:E(_Hm),e:E(_Hn),f:E(_Ho),g:E(_HA),h:_GF+_HC|0,i:_HE,j:E(_Hg)+1|0,k:_Hp,l:E(_Hq),m:_Hr,n:E(_Hs),o:E(_Ht),p:(_GF+_HC|0)<=_HD,q:E(_Hu),r:E(_Hv),s:E(_Hw),t:E(_Hx),u:E(_Hy),v:_Hz};}else{var _HF=E(_H1);return (!E(_H9))?{_:0,a:E(_Hj),b:E(_Hk),c:E(_Hl),d:E(_Hm),e:E(_Hn),f:E(_Ho),g:E(_HA),h:0,i:_HF,j:E(_Hg),k:_Hp,l:E(_Hq),m:_Hr,n:E(_Hs),o:E(_Ht),p:(_GF+_HC|0)<=_HD,q:E(_Hu),r:E(_Hv),s:E(_Hw),t:E(_Hx),u:E(_Hy),v:_Hz}:{_:0,a:E(_Hj),b:E(_Hk),c:E(_Hl),d:E(_Hm),e:E(_Hn),f:E(_Ho),g:E(_HA),h:0,i:_HF,j:E(_Hg)+1|0,k:_Hp,l:E(_Hq),m:_Hr,n:E(_Hs),o:E(_Ht),p:(_GF+_HC|0)<=_HD,q:E(_Hu),r:E(_Hv),s:E(_Hw),t:E(_Hx),u:E(_Hy),v:_Hz};}};if(!E(_GZ)){if(!E(_Hb)){return B(_HB(1));}else{return B(_HB(B(_7a(_Hc,0))+2|0));}}else{return B(_HB(B(_7a(_Ha,0))+2|0));}});};if(!E(_GZ)){if(!E(_Hb)){if(!E(_H9)){var _HG=B(A(_D0,[E(_Gn).a,_H2,_E9,_cl,_H5,_H6,_GY,_]));return new F(function(){return _Hh(_);});}else{var _HH=E(_Gn),_HI=_HH.a,_HJ=_HH.b,_HK=B(_es(_HI,_HJ,_Hd,_)),_HL=B(_Fy(_HI,_HJ,_Ec,_H3,new T(function(){return (15+E(_Hg)|0)+1|0;}),_H3,B(_eI(_GV,_Gz)),_));return new F(function(){return _Hh(_);});}}else{var _HM=E(_Hd);if(!E(_HM.t)){return new F(function(){return _Hh(_);});}else{var _HN=E(_Gn),_HO=_HN.a,_HP=_HN.b,_HQ=B(_es(_HO,_HP,_HM,_)),_HR=B(_Fy(_HO,_HP,_Ec,_H3,new T(function(){return 15+E(_Hg)|0;}),_H3,B(_E4(_HM.c,new T(function(){return E(B(_fc(_HM.l)).a);},1),_HM.m)),_));return new F(function(){return _Hh(_);});}}}else{var _HS=new T(function(){if(E(_H3)!=E(_H6)){return E(_H5);}else{return E(_H5)+1|0;}}),_HT=new T(function(){var _HU=E(_H6);if(E(_H3)!=_HU){return _HU-1|0;}else{return E(_Dn);}}),_HV=E(_Ha);if(!_HV._){return new F(function(){return _Hh(_);});}else{var _HW=E(_DD);if(!_HW._){return new F(function(){return _Hh(_);});}else{var _HX=E(_Gn).a,_HY=B(A(_D0,[_HX,_H2,_F6,_HW.a,_HS,_HT,_HV.a,_])),_HZ=function(_I0,_I1,_){while(1){var _I2=E(_I0);if(!_I2._){return _7f;}else{var _I3=E(_I1);if(!_I3._){return _7f;}else{var _I4=B(A(_D0,[_HX,_H2,_F6,_I3.a,_HS,_HT,_I2.a,_]));_I0=_I2.b;_I1=_I3.b;continue;}}}},_I5=B(_HZ(_HV.b,_HW.b,_));return new F(function(){return _Hh(_);});}}}},_I6=E(_GW);switch(_I6){case 125:return new F(function(){return _GX(32);});break;case 12289:return new F(function(){return _GX(32);});break;case 12290:return new F(function(){return _GX(32);});break;default:return new F(function(){return _GX(_I6);});}}}else{return {_:0,a:E({_:0,a:E(_Go),b:E(_Gp),c:_Gq,d:_Gr,e:_Gs,f:_Gt,g:E(_Gu),h:E(_Gv),i:E(_Gw)}),b:E(new T2(0,_Gx,_Gy)),c:E(_Gz),d:E(_GA),e:E(_GB),f:E(_GC),g:E(_GU),h:_GF,i:_GG,j:_GH,k:_GI,l:E(_GJ),m:_GK,n:E(_GL),o:E(_GM),p:E(_kr),q:E(_kr),r:E(_GP),s:E(_GQ),t:E(_GR),u:E(_GS),v:_GT};}}},_I7=function(_I8,_I9,_Ia,_Ib,_Ic,_Id,_Ie,_If,_Ig,_Ih,_Ii,_Ij,_Ik,_Il,_Im,_In,_Io,_Ip,_Iq,_Ir,_Is,_It,_Iu,_Iv,_Iw,_Ix,_Iy,_Iz,_IA,_IB,_IC,_ID,_IE,_){while(1){var _IF=B(_Gm(_I8,_I9,_Ia,_Ib,_Ic,_Id,_Ie,_If,_Ig,_Ih,_Ii,_Ij,_Ik,_Il,_Im,_In,_Io,_Ip,_Iq,_Ir,_Is,_It,_Iu,_Iv,_Iw,_Ix,_Iy,_Iz,_IA,_IB,_IC,_ID,_IE,_)),_IG=E(_IF),_IH=_IG.c,_II=_IG.d,_IJ=_IG.e,_IK=_IG.f,_IL=_IG.h,_IM=_IG.i,_IN=_IG.j,_IO=_IG.k,_IP=_IG.l,_IQ=_IG.m,_IR=_IG.n,_IS=_IG.o,_IT=_IG.p,_IU=_IG.r,_IV=_IG.t,_IW=_IG.u,_IX=_IG.v,_IY=E(_IG.a),_IZ=E(_IG.b),_J0=E(_IG.g);if(!E(_IG.q)){if(!E(_Iy)){return {_:0,a:E(_IY),b:E(_IZ),c:E(_IH),d:E(_II),e:E(_IJ),f:E(_IK),g:E(_J0),h:_IL,i:_IM,j:_IN,k:_IO,l:E(_IP),m:_IQ,n:E(_IR),o:E(_IS),p:E(_IT),q:E(_qO),r:E(_IU),s:E(_qO),t:E(_IV),u:E(_IW),v:_IX};}else{_I9=_IY.a;_Ia=_IY.b;_Ib=_IY.c;_Ic=_IY.d;_Id=_IY.e;_Ie=_IY.f;_If=_IY.g;_Ig=_IY.h;_Ih=_IY.i;_Ii=_IZ.a;_Ij=_IZ.b;_Ik=_IH;_Il=_II;_Im=_IJ;_In=_IK;_Io=_J0.a;_Ip=_J0.b;_Iq=_IL;_Ir=_IM;_Is=_IN;_It=_IO;_Iu=_IP;_Iv=_IQ;_Iw=_IR;_Ix=_IS;_Iy=_IT;_Iz=_qO;_IA=_IU;_IB=_IG.s;_IC=_IV;_ID=_IW;_IE=_IX;continue;}}else{return {_:0,a:E(_IY),b:E(_IZ),c:E(_IH),d:E(_II),e:E(_IJ),f:E(_IK),g:E(_J0),h:_IL,i:_IM,j:_IN,k:_IO,l:E(_IP),m:_IQ,n:E(_IR),o:E(_IS),p:E(_IT),q:E(_kr),r:E(_IU),s:E(_qO),t:E(_IV),u:E(_IW),v:_IX};}}},_J1=function(_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk,_Jl,_Jm,_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_){var _Jy=B(_Gm(_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk,_Jl,_Jm,_Jn,_Jo,_Jp,_Jq,_Jr,_kr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_)),_Jz=E(_Jy),_JA=_Jz.c,_JB=_Jz.d,_JC=_Jz.e,_JD=_Jz.f,_JE=_Jz.h,_JF=_Jz.i,_JG=_Jz.j,_JH=_Jz.k,_JI=_Jz.l,_JJ=_Jz.m,_JK=_Jz.n,_JL=_Jz.o,_JM=_Jz.p,_JN=_Jz.r,_JO=_Jz.t,_JP=_Jz.u,_JQ=_Jz.v,_JR=E(_Jz.a),_JS=E(_Jz.b),_JT=E(_Jz.g);if(!E(_Jz.q)){return new F(function(){return _I7(_J2,_JR.a,_JR.b,_JR.c,_JR.d,_JR.e,_JR.f,_JR.g,_JR.h,_JR.i,_JS.a,_JS.b,_JA,_JB,_JC,_JD,_JT.a,_JT.b,_JE,_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_qO,_JN,_Jz.s,_JO,_JP,_JQ,_);});}else{return {_:0,a:E(_JR),b:E(_JS),c:E(_JA),d:E(_JB),e:E(_JC),f:E(_JD),g:E(_JT),h:_JE,i:_JF,j:_JG,k:_JH,l:E(_JI),m:_JJ,n:E(_JK),o:E(_JL),p:E(_JM),q:E(_kr),r:E(_JN),s:E(_qO),t:E(_JO),u:E(_JP),v:_JQ};}},_JU=new T1(0,0),_JV=function(_JW,_JX){while(1){var _JY=E(_JW);if(!_JY._){var _JZ=_JY.a,_K0=E(_JX);if(!_K0._){return new T1(0,(_JZ>>>0|_K0.a>>>0)>>>0&4294967295);}else{_JW=new T1(1,I_fromInt(_JZ));_JX=_K0;continue;}}else{var _K1=E(_JX);if(!_K1._){_JW=_JY;_JX=new T1(1,I_fromInt(_K1.a));continue;}else{return new T1(1,I_or(_JY.a,_K1.a));}}}},_K2=function(_K3){var _K4=E(_K3);if(!_K4._){return E(_JU);}else{return new F(function(){return _JV(new T1(0,E(_K4.a)),B(_8J(B(_K2(_K4.b)),31)));});}},_K5=function(_K6,_K7){if(!E(_K6)){return new F(function(){return _bo(B(_K2(_K7)));});}else{return new F(function(){return _K2(_K7);});}},_K8=1420103680,_K9=465,_Ka=new T2(1,_K9,_10),_Kb=new T2(1,_K8,_Ka),_Kc=new T(function(){return B(_K5(_kr,_Kb));}),_Kd=function(_Ke){return E(_Kc);},_Kf=0,_Kg=function(_Kh,_Ki){var _Kj=_Kh%_Ki;if(_Kh<=0){if(_Kh>=0){return E(_Kj);}else{if(_Ki<=0){return E(_Kj);}else{var _Kk=E(_Kj);return (_Kk==0)?0:_Kk+_Ki|0;}}}else{if(_Ki>=0){if(_Kh>=0){return E(_Kj);}else{if(_Ki<=0){return E(_Kj);}else{var _Kl=E(_Kj);return (_Kl==0)?0:_Kl+_Ki|0;}}}else{var _Km=E(_Kj);return (_Km==0)?0:_Km+_Ki|0;}}},_Kn=function(_Ko,_Kp){var _Kq=E(_Kp);switch(_Kq){case  -1:return E(_Kf);case 0:return E(_8a);default:return new F(function(){return _Kg(E(_Ko),_Kq);});}},_Kr=new T(function(){return B(unCStr("s"));}),_Ks=function(_Kt,_Ku){while(1){var _Kv=E(_Kt);if(!_Kv._){return E(_Ku);}else{_Kt=_Kv.b;_Ku=_Kv.a;continue;}}},_Kw=function(_Kx,_Ky,_Kz){return new F(function(){return _Ks(_Ky,_Kx);});},_KA=new T1(0,1),_KB=function(_KC,_KD){var _KE=E(_KC);return new T2(0,_KE,new T(function(){var _KF=B(_KB(B(_8q(_KE,_KD)),_KD));return new T2(1,_KF.a,_KF.b);}));},_KG=function(_KH){var _KI=B(_KB(_KH,_KA));return new T2(1,_KI.a,_KI.b);},_KJ=function(_KK,_KL){var _KM=B(_KB(_KK,new T(function(){return B(_aJ(_KL,_KK));})));return new T2(1,_KM.a,_KM.b);},_KN=new T1(0,0),_KO=function(_KP,_KQ){var _KR=E(_KP);if(!_KR._){var _KS=_KR.a,_KT=E(_KQ);return (_KT._==0)?_KS>=_KT.a:I_compareInt(_KT.a,_KS)<=0;}else{var _KU=_KR.a,_KV=E(_KQ);return (_KV._==0)?I_compareInt(_KU,_KV.a)>=0:I_compare(_KU,_KV.a)>=0;}},_KW=function(_KX,_KY,_KZ){if(!B(_KO(_KY,_KN))){var _L0=function(_L1){return (!B(_92(_L1,_KZ)))?new T2(1,_L1,new T(function(){return B(_L0(B(_8q(_L1,_KY))));})):__Z;};return new F(function(){return _L0(_KX);});}else{var _L2=function(_L3){return (!B(_8T(_L3,_KZ)))?new T2(1,_L3,new T(function(){return B(_L2(B(_8q(_L3,_KY))));})):__Z;};return new F(function(){return _L2(_KX);});}},_L4=function(_L5,_L6,_L7){return new F(function(){return _KW(_L5,B(_aJ(_L6,_L5)),_L7);});},_L8=function(_L9,_La){return new F(function(){return _KW(_L9,_KA,_La);});},_Lb=function(_Lc){return new F(function(){return _8n(_Lc);});},_Ld=function(_Le){return new F(function(){return _aJ(_Le,_KA);});},_Lf=function(_Lg){return new F(function(){return _8q(_Lg,_KA);});},_Lh=function(_Li){return new F(function(){return _pB(E(_Li));});},_Lj={_:0,a:_Lf,b:_Ld,c:_Lh,d:_Lb,e:_KG,f:_KJ,g:_L8,h:_L4},_Lk=function(_Ll,_Lm){if(_Ll<=0){if(_Ll>=0){return new F(function(){return quot(_Ll,_Lm);});}else{if(_Lm<=0){return new F(function(){return quot(_Ll,_Lm);});}else{return quot(_Ll+1|0,_Lm)-1|0;}}}else{if(_Lm>=0){if(_Ll>=0){return new F(function(){return quot(_Ll,_Lm);});}else{if(_Lm<=0){return new F(function(){return quot(_Ll,_Lm);});}else{return quot(_Ll+1|0,_Lm)-1|0;}}}else{return quot(_Ll-1|0,_Lm)-1|0;}}},_Ln=function(_Lo,_Lp){while(1){var _Lq=E(_Lo);if(!_Lq._){var _Lr=E(_Lq.a);if(_Lr==( -2147483648)){_Lo=new T1(1,I_fromInt( -2147483648));continue;}else{var _Ls=E(_Lp);if(!_Ls._){return new T1(0,B(_Lk(_Lr,_Ls.a)));}else{_Lo=new T1(1,I_fromInt(_Lr));_Lp=_Ls;continue;}}}else{var _Lt=_Lq.a,_Lu=E(_Lp);return (_Lu._==0)?new T1(1,I_div(_Lt,I_fromInt(_Lu.a))):new T1(1,I_div(_Lt,_Lu.a));}}},_Lv=new T1(0,0),_Lw=function(_Lx,_Ly){if(!B(_8f(_Ly,_Lv))){return new F(function(){return _Ln(_Lx,_Ly);});}else{return E(_8a);}},_Lz=function(_LA,_LB){while(1){var _LC=E(_LA);if(!_LC._){var _LD=E(_LC.a);if(_LD==( -2147483648)){_LA=new T1(1,I_fromInt( -2147483648));continue;}else{var _LE=E(_LB);if(!_LE._){var _LF=_LE.a;return new T2(0,new T1(0,B(_Lk(_LD,_LF))),new T1(0,B(_Kg(_LD,_LF))));}else{_LA=new T1(1,I_fromInt(_LD));_LB=_LE;continue;}}}else{var _LG=E(_LB);if(!_LG._){_LA=_LC;_LB=new T1(1,I_fromInt(_LG.a));continue;}else{var _LH=I_divMod(_LC.a,_LG.a);return new T2(0,new T1(1,_LH.a),new T1(1,_LH.b));}}}},_LI=function(_LJ,_LK){if(!B(_8f(_LK,_Lv))){var _LL=B(_Lz(_LJ,_LK));return new T2(0,_LL.a,_LL.b);}else{return E(_8a);}},_LM=function(_LN,_LO){while(1){var _LP=E(_LN);if(!_LP._){var _LQ=E(_LP.a);if(_LQ==( -2147483648)){_LN=new T1(1,I_fromInt( -2147483648));continue;}else{var _LR=E(_LO);if(!_LR._){return new T1(0,B(_Kg(_LQ,_LR.a)));}else{_LN=new T1(1,I_fromInt(_LQ));_LO=_LR;continue;}}}else{var _LS=_LP.a,_LT=E(_LO);return (_LT._==0)?new T1(1,I_mod(_LS,I_fromInt(_LT.a))):new T1(1,I_mod(_LS,_LT.a));}}},_LU=function(_LV,_LW){if(!B(_8f(_LW,_Lv))){return new F(function(){return _LM(_LV,_LW);});}else{return E(_8a);}},_LX=function(_LY,_LZ){while(1){var _M0=E(_LY);if(!_M0._){var _M1=E(_M0.a);if(_M1==( -2147483648)){_LY=new T1(1,I_fromInt( -2147483648));continue;}else{var _M2=E(_LZ);if(!_M2._){return new T1(0,quot(_M1,_M2.a));}else{_LY=new T1(1,I_fromInt(_M1));_LZ=_M2;continue;}}}else{var _M3=_M0.a,_M4=E(_LZ);return (_M4._==0)?new T1(0,I_toInt(I_quot(_M3,I_fromInt(_M4.a)))):new T1(1,I_quot(_M3,_M4.a));}}},_M5=function(_M6,_M7){if(!B(_8f(_M7,_Lv))){return new F(function(){return _LX(_M6,_M7);});}else{return E(_8a);}},_M8=function(_M9,_Ma){if(!B(_8f(_Ma,_Lv))){var _Mb=B(_8z(_M9,_Ma));return new T2(0,_Mb.a,_Mb.b);}else{return E(_8a);}},_Mc=function(_Md,_Me){while(1){var _Mf=E(_Md);if(!_Mf._){var _Mg=E(_Mf.a);if(_Mg==( -2147483648)){_Md=new T1(1,I_fromInt( -2147483648));continue;}else{var _Mh=E(_Me);if(!_Mh._){return new T1(0,_Mg%_Mh.a);}else{_Md=new T1(1,I_fromInt(_Mg));_Me=_Mh;continue;}}}else{var _Mi=_Mf.a,_Mj=E(_Me);return (_Mj._==0)?new T1(1,I_rem(_Mi,I_fromInt(_Mj.a))):new T1(1,I_rem(_Mi,_Mj.a));}}},_Mk=function(_Ml,_Mm){if(!B(_8f(_Mm,_Lv))){return new F(function(){return _Mc(_Ml,_Mm);});}else{return E(_8a);}},_Mn=function(_Mo){return E(_Mo);},_Mp=function(_Mq){return E(_Mq);},_Mr=function(_Ms){var _Mt=E(_Ms);if(!_Mt._){var _Mu=E(_Mt.a);return (_Mu==( -2147483648))?E(_bn):(_Mu<0)?new T1(0, -_Mu):E(_Mt);}else{var _Mv=_Mt.a;return (I_compareInt(_Mv,0)>=0)?E(_Mt):new T1(1,I_negate(_Mv));}},_Mw=new T1(0, -1),_Mx=function(_My){var _Mz=E(_My);if(!_Mz._){var _MA=_Mz.a;return (_MA>=0)?(E(_MA)==0)?E(_JU):E(_91):E(_Mw);}else{var _MB=I_compareInt(_Mz.a,0);return (_MB<=0)?(E(_MB)==0)?E(_JU):E(_Mw):E(_91);}},_MC={_:0,a:_8q,b:_aJ,c:_pH,d:_bo,e:_Mr,f:_Mx,g:_Mp},_MD=function(_ME,_MF){var _MG=E(_ME);if(!_MG._){var _MH=_MG.a,_MI=E(_MF);return (_MI._==0)?_MH!=_MI.a:(I_compareInt(_MI.a,_MH)==0)?false:true;}else{var _MJ=_MG.a,_MK=E(_MF);return (_MK._==0)?(I_compareInt(_MJ,_MK.a)==0)?false:true:(I_compare(_MJ,_MK.a)==0)?false:true;}},_ML=new T2(0,_8f,_MD),_MM=function(_MN,_MO){return (!B(_au(_MN,_MO)))?E(_MN):E(_MO);},_MP=function(_MQ,_MR){return (!B(_au(_MQ,_MR)))?E(_MR):E(_MQ);},_MS={_:0,a:_ML,b:_7q,c:_92,d:_au,e:_8T,f:_KO,g:_MM,h:_MP},_MT=function(_MU){return new T2(0,E(_MU),E(_c7));},_MV=new T3(0,_MC,_MS,_MT),_MW={_:0,a:_MV,b:_Lj,c:_M5,d:_Mk,e:_Lw,f:_LU,g:_M8,h:_LI,i:_Mn},_MX=new T1(0,0),_MY=function(_MZ,_N0,_N1){var _N2=B(A1(_MZ,_N0));if(!B(_8f(_N2,_MX))){return new F(function(){return _Ln(B(_pH(_N0,_N1)),_N2);});}else{return E(_8a);}},_N3=function(_N4,_N5){while(1){if(!B(_8f(_N5,_Lv))){var _N6=_N5,_N7=B(_Mk(_N4,_N5));_N4=_N6;_N5=_N7;continue;}else{return E(_N4);}}},_N8=5,_N9=new T(function(){return B(_86(_N8));}),_Na=new T(function(){return die(_N9);}),_Nb=function(_Nc,_Nd){if(!B(_8f(_Nd,_Lv))){var _Ne=B(_N3(B(_Mr(_Nc)),B(_Mr(_Nd))));return (!B(_8f(_Ne,_Lv)))?new T2(0,B(_LX(_Nc,_Ne)),B(_LX(_Nd,_Ne))):E(_8a);}else{return E(_Na);}},_Nf=function(_Ng,_Nh,_Ni,_Nj){var _Nk=B(_pH(_Nh,_Ni));return new F(function(){return _Nb(B(_pH(B(_pH(_Ng,_Nj)),B(_Mx(_Nk)))),B(_Mr(_Nk)));});},_Nl=function(_Nm){return E(E(_Nm).a);},_Nn=function(_No){return E(E(_No).a);},_Np=function(_Nq,_Nr,_Ns){var _Nt=new T(function(){if(!B(_8f(_Ns,_Lv))){var _Nu=B(_8z(_Nr,_Ns));return new T2(0,_Nu.a,_Nu.b);}else{return E(_8a);}}),_Nv=new T(function(){return B(A2(_cc,B(_Nn(B(_Nl(_Nq)))),new T(function(){return E(E(_Nt).a);})));});return new T2(0,_Nv,new T(function(){return new T2(0,E(E(_Nt).b),E(_Ns));}));},_Nw=function(_Nx,_Ny,_Nz){var _NA=B(_Np(_Nx,_Ny,_Nz)),_NB=_NA.a,_NC=E(_NA.b);if(!B(_92(B(_pH(_NC.a,_c7)),B(_pH(_Lv,_NC.b))))){return E(_NB);}else{var _ND=B(_Nn(B(_Nl(_Nx))));return new F(function(){return A3(_Dr,_ND,_NB,new T(function(){return B(A2(_cc,_ND,_c7));}));});}},_NE=479723520,_NF=40233135,_NG=new T2(1,_NF,_10),_NH=new T2(1,_NE,_NG),_NI=new T(function(){return B(_K5(_kr,_NH));}),_NJ=new T1(0,40587),_NK=function(_NL){var _NM=new T(function(){var _NN=B(_Nf(_NL,_c7,_Kc,_c7)),_NO=B(_Nf(_NI,_c7,_Kc,_c7)),_NP=B(_Nf(_NN.a,_NN.b,_NO.a,_NO.b));return B(_Nw(_MW,_NP.a,_NP.b));});return new T2(0,new T(function(){return B(_8q(_NJ,_NM));}),new T(function(){return B(_aJ(_NL,B(_MY(_Kd,B(_pH(_NM,_Kc)),_NI))));}));},_NQ=function(_NR,_){var _NS=__get(_NR,0),_NT=__get(_NR,1),_NU=Number(_NS),_NV=jsTrunc(_NU),_NW=Number(_NT),_NX=jsTrunc(_NW);return new T2(0,_NV,_NX);},_NY=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_NZ=660865024,_O0=465661287,_O1=new T2(1,_O0,_10),_O2=new T2(1,_NZ,_O1),_O3=new T(function(){return B(_K5(_kr,_O2));}),_O4=function(_){var _O5=__app0(E(_NY)),_O6=B(_NQ(_O5,_));return new T(function(){var _O7=E(_O6);if(!B(_8f(_O3,_MX))){return B(_8q(B(_pH(B(_pB(E(_O7.a))),_Kc)),B(_Ln(B(_pH(B(_pH(B(_pB(E(_O7.b))),_Kc)),_Kc)),_O3))));}else{return E(_8a);}});},_O8=new T(function(){return B(err(_mA));}),_O9=new T(function(){return B(err(_my));}),_Oa=new T(function(){return B(A3(_yt,_yW,_xY,_z3));}),_Ob=new T1(0,1),_Oc=new T1(0,10),_Od=function(_Oe){while(1){var _Of=E(_Oe);if(!_Of._){_Oe=new T1(1,I_fromInt(_Of.a));continue;}else{return new F(function(){return I_toString(_Of.a);});}}},_Og=function(_Oh,_Oi){return new F(function(){return _y(fromJSStr(B(_Od(_Oh))),_Oi);});},_Oj=new T1(0,0),_Ok=function(_Ol,_Om,_On){if(_Ol<=6){return new F(function(){return _Og(_Om,_On);});}else{if(!B(_92(_Om,_Oj))){return new F(function(){return _Og(_Om,_On);});}else{return new T2(1,_H,new T(function(){return B(_y(fromJSStr(B(_Od(_Om))),new T2(1,_G,_On)));}));}}},_Oo=function(_Op,_Oq,_Or){while(1){if(!(_Oq%2)){var _Os=B(_pH(_Op,_Op)),_Ot=quot(_Oq,2);_Op=_Os;_Oq=_Ot;continue;}else{var _Ou=E(_Oq);if(_Ou==1){return new F(function(){return _pH(_Op,_Or);});}else{var _Os=B(_pH(_Op,_Op)),_Ov=B(_pH(_Op,_Or));_Op=_Os;_Oq=quot(_Ou-1|0,2);_Or=_Ov;continue;}}}},_Ow=function(_Ox,_Oy){while(1){if(!(_Oy%2)){var _Oz=B(_pH(_Ox,_Ox)),_OA=quot(_Oy,2);_Ox=_Oz;_Oy=_OA;continue;}else{var _OB=E(_Oy);if(_OB==1){return E(_Ox);}else{return new F(function(){return _Oo(B(_pH(_Ox,_Ox)),quot(_OB-1|0,2),_Ox);});}}}},_OC=new T(function(){return B(unCStr("Negative exponent"));}),_OD=new T(function(){return B(err(_OC));}),_OE=function(_OF){return new F(function(){return _Ok(0,_OF,_10);});},_OG=new T(function(){return B(_8f(_Oc,_MX));}),_OH=function(_OI){while(1){if(!B(_8f(_OI,_MX))){if(!E(_OG)){if(!B(_8f(B(_LM(_OI,_Oc)),_MX))){return new F(function(){return _OE(_OI);});}else{var _OJ=B(_Ln(_OI,_Oc));_OI=_OJ;continue;}}else{return E(_8a);}}else{return __Z;}}},_OK=46,_OL=48,_OM=function(_ON,_OO,_OP){if(!B(_92(_OP,_MX))){var _OQ=B(A1(_ON,_OP));if(!B(_8f(_OQ,_MX))){var _OR=B(_Lz(_OP,_OQ)),_OS=_OR.b,_OT=new T(function(){var _OU=Math.log(B(_bH(_OQ)))/Math.log(10),_OV=_OU&4294967295,_OW=function(_OX){if(_OX>=0){var _OY=E(_OX);if(!_OY){var _OZ=B(_Ln(B(_aJ(B(_8q(B(_pH(_OS,_c7)),_OQ)),_Ob)),_OQ));}else{var _OZ=B(_Ln(B(_aJ(B(_8q(B(_pH(_OS,B(_Ow(_Oc,_OY)))),_OQ)),_Ob)),_OQ));}var _P0=function(_P1){var _P2=B(_Ok(0,_OZ,_10)),_P3=_OX-B(_7a(_P2,0))|0;if(0>=_P3){if(!E(_OO)){return E(_P2);}else{return new F(function(){return _OH(_OZ);});}}else{var _P4=new T(function(){if(!E(_OO)){return E(_P2);}else{return B(_OH(_OZ));}}),_P5=function(_P6){var _P7=E(_P6);return (_P7==1)?E(new T2(1,_OL,_P4)):new T2(1,_OL,new T(function(){return B(_P5(_P7-1|0));}));};return new F(function(){return _P5(_P3);});}};if(!E(_OO)){var _P8=B(_P0(_));return (_P8._==0)?__Z:new T2(1,_OK,_P8);}else{if(!B(_8f(_OZ,_MX))){var _P9=B(_P0(_));return (_P9._==0)?__Z:new T2(1,_OK,_P9);}else{return __Z;}}}else{return E(_OD);}};if(_OV>=_OU){return B(_OW(_OV));}else{return B(_OW(_OV+1|0));}},1);return new F(function(){return _y(B(_Ok(0,_OR.a,_10)),_OT);});}else{return E(_8a);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_OM(_ON,_OO,B(_bo(_OP))));}));});}},_Pa=function(_Pb,_Pc,_){var _Pd=B(_O4(_)),_Pe=new T(function(){var _Pf=new T(function(){var _Pg=new T(function(){var _Ph=B(_y(B(_OM(_Kd,_kr,B(_NK(_Pd)).b)),_Kr));if(!_Ph._){return E(_Bf);}else{var _Pi=B(_Ba(_Ph.a,_Ph.b));if(!_Pi._){return B(_Kw(_10,_10,_Dm));}else{var _Pj=_Pi.a,_Pk=E(_Pi.b);if(!_Pk._){return B(_Kw(new T2(1,_Pj,_10),_10,_Dm));}else{var _Pl=E(_Pj),_Pm=new T(function(){var _Pn=B(_ky(46,_Pk.a,_Pk.b));return new T2(0,_Pn.a,_Pn.b);});if(E(_Pl)==46){return B(_Kw(_10,new T2(1,new T(function(){return E(E(_Pm).a);}),new T(function(){return E(E(_Pm).b);})),_Dm));}else{return B(_Kw(new T2(1,_Pl,new T(function(){return E(E(_Pm).a);})),new T(function(){return E(E(_Pm).b);}),_Dm));}}}}}),_Po=B(_za(B(_mJ(_Oa,_Pg))));if(!_Po._){return E(_O9);}else{if(!E(_Po.b)._){return B(_eI(3,B(_I(0,E(_Po.a)+(imul(E(_Pc),E(_Pb)-1|0)|0)|0,_10))));}else{return E(_O8);}}}),_Pp=B(_za(B(_mJ(_Oa,_Pf))));if(!_Pp._){return E(_O9);}else{if(!E(_Pp.b)._){return E(_Pp.a);}else{return E(_O8);}}});return new T2(0,new T(function(){return B(_Kn(_Pe,_Pb));}),_Pe);},_Pq=function(_Pr){var _Ps=E(_Pr);if(!_Ps._){return new T2(0,_10,_10);}else{var _Pt=E(_Ps.a),_Pu=new T(function(){var _Pv=B(_Pq(_Ps.b));return new T2(0,_Pv.a,_Pv.b);});return new T2(0,new T2(1,_Pt.a,new T(function(){return E(E(_Pu).a);})),new T2(1,_Pt.b,new T(function(){return E(E(_Pu).b);})));}},_Pw=function(_Px){return new F(function(){return _kt("Check.hs:66:21-47|(l : r : _)");});},_Py=new T(function(){return B(_Pw(_));}),_Pz=61,_PA=function(_PB,_PC){while(1){var _PD=E(_PB);if(!_PD._){return E(_PC);}else{_PB=_PD.b;_PC=_PD.a;continue;}}},_PE=function(_PF,_PG,_PH){return new F(function(){return _PA(_PG,_PF);});},_PI=function(_PJ,_PK){var _PL=E(_PK);if(!_PL._){return new T2(0,_10,_10);}else{var _PM=_PL.a;if(!B(A1(_PJ,_PM))){var _PN=new T(function(){var _PO=B(_PI(_PJ,_PL.b));return new T2(0,_PO.a,_PO.b);});return new T2(0,new T2(1,_PM,new T(function(){return E(E(_PN).a);})),new T(function(){return E(E(_PN).b);}));}else{return new T2(0,_10,_PL);}}},_PP=function(_PQ,_PR){while(1){var _PS=E(_PR);if(!_PS._){return __Z;}else{if(!B(A1(_PQ,_PS.a))){return E(_PS);}else{_PR=_PS.b;continue;}}}},_PT=function(_PU){var _PV=_PU>>>0;if(_PV>887){var _PW=u_iswspace(_PU);return (E(_PW)==0)?false:true;}else{var _PX=E(_PV);return (_PX==32)?true:(_PX-9>>>0>4)?(E(_PX)==160)?true:false:true;}},_PY=function(_PZ){return new F(function(){return _PT(E(_PZ));});},_Q0=function(_Q1){var _Q2=B(_PP(_PY,_Q1));if(!_Q2._){return __Z;}else{var _Q3=new T(function(){var _Q4=B(_PI(_PY,_Q2));return new T2(0,_Q4.a,_Q4.b);});return new T2(1,new T(function(){return E(E(_Q3).a);}),new T(function(){return B(_Q0(E(_Q3).b));}));}},_Q5=function(_Q6){if(!B(_4B(_6f,_Pz,_Q6))){return new T2(0,_Q6,_10);}else{var _Q7=new T(function(){var _Q8=E(_Q6);if(!_Q8._){return E(_Py);}else{var _Q9=E(_Q8.b);if(!_Q9._){return E(_Py);}else{var _Qa=_Q9.a,_Qb=_Q9.b,_Qc=E(_Q8.a);if(E(_Qc)==61){return new T2(0,_10,new T(function(){return E(B(_ky(61,_Qa,_Qb)).a);}));}else{var _Qd=B(_ky(61,_Qa,_Qb)),_Qe=E(_Qd.b);if(!_Qe._){return E(_Py);}else{return new T2(0,new T2(1,_Qc,_Qd.a),_Qe.a);}}}}});return new T2(0,new T(function(){var _Qf=B(_Q0(E(_Q7).a));if(!_Qf._){return __Z;}else{return B(_PE(_Qf.a,_Qf.b,_Dm));}}),new T(function(){var _Qg=B(_Q0(E(_Q7).b));if(!_Qg._){return __Z;}else{return E(_Qg.a);}}));}},_Qh=new T(function(){return B(unCStr("+-*^"));}),_Qi=new T(function(){return B(unCStr("0123456789"));}),_Qj=new T(function(){return B(_kt("Siki.hs:12:9-28|(hn : ns, cs)"));}),_Qk=new T2(1,_10,_10),_Ql=function(_Qm){var _Qn=E(_Qm);if(!_Qn._){return new T2(0,_Qk,_10);}else{var _Qo=_Qn.a,_Qp=new T(function(){var _Qq=B(_Ql(_Qn.b)),_Qr=E(_Qq.a);if(!_Qr._){return E(_Qj);}else{return new T3(0,_Qr.a,_Qr.b,_Qq.b);}});return (!B(_4B(_6f,_Qo,_Qi)))?(!B(_4B(_6f,_Qo,_Qh)))?new T2(0,new T2(1,new T2(1,_Qo,new T(function(){return E(E(_Qp).a);})),new T(function(){return E(E(_Qp).b);})),new T(function(){return E(E(_Qp).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_Qp).a);}),new T(function(){return E(E(_Qp).b);}))),new T2(1,_Qo,new T(function(){return E(E(_Qp).c);}))):new T2(0,new T2(1,new T2(1,_Qo,new T(function(){return E(E(_Qp).a);})),new T(function(){return E(E(_Qp).b);})),new T(function(){return E(E(_Qp).c);}));}},_Qs=function(_Qt,_Qu){while(1){var _Qv=E(_Qu);if(!_Qv._){return __Z;}else{var _Qw=_Qv.b,_Qx=E(_Qt);if(_Qx==1){return E(_Qw);}else{_Qt=_Qx-1|0;_Qu=_Qw;continue;}}}},_Qy=function(_Qz,_QA){while(1){var _QB=E(_QA);if(!_QB._){return __Z;}else{var _QC=_QB.b,_QD=E(_Qz);if(_QD==1){return E(_QC);}else{_Qz=_QD-1|0;_QA=_QC;continue;}}}},_QE=function(_QF,_QG){while(1){var _QH=E(_QF);if(!_QH._){return E(_QG);}else{var _QI=new T2(1,_QH.a,_QG);_QF=_QH.b;_QG=_QI;continue;}}},_QJ=function(_QK){return new F(function(){return _QE(_QK,_10);});},_QL=function(_QM,_QN,_QO,_QP){var _QQ=new T(function(){return B(_iC(_6f,_QN,_QO));}),_QR=new T(function(){var _QS=E(_QQ),_QT=new T(function(){var _QU=_QS+1|0;if(_QU>0){return B(_Qy(_QU,_QO));}else{return E(_QO);}});if(0>=_QS){return E(_QT);}else{var _QV=function(_QW,_QX){var _QY=E(_QW);if(!_QY._){return E(_QT);}else{var _QZ=_QY.a,_R0=E(_QX);return (_R0==1)?new T2(1,_QZ,_QT):new T2(1,_QZ,new T(function(){return B(_QV(_QY.b,_R0-1|0));}));}};return B(_QV(_QO,_QS));}}),_R1=new T(function(){var _R2=E(_QQ),_R3=new T(function(){if(E(_QN)==94){return B(A2(_QM,new T(function(){return B(_77(_QP,_R2+1|0));}),new T(function(){return B(_77(_QP,_R2));})));}else{return B(A2(_QM,new T(function(){return B(_77(_QP,_R2));}),new T(function(){return B(_77(_QP,_R2+1|0));})));}}),_R4=new T2(1,_R3,new T(function(){var _R5=_R2+2|0;if(_R5>0){return B(_Qs(_R5,_QP));}else{return E(_QP);}}));if(0>=_R2){return E(_R4);}else{var _R6=function(_R7,_R8){var _R9=E(_R7);if(!_R9._){return E(_R4);}else{var _Ra=_R9.a,_Rb=E(_R8);return (_Rb==1)?new T2(1,_Ra,_R4):new T2(1,_Ra,new T(function(){return B(_R6(_R9.b,_Rb-1|0));}));}};return B(_R6(_QP,_R2));}});return (E(_QN)==94)?new T2(0,new T(function(){return B(_QJ(_QR));}),new T(function(){return B(_QJ(_R1));})):new T2(0,_QR,_R1);},_Rc=new T1(0,2),_Rd=new T(function(){return B(_8f(_Rc,_Lv));}),_Re=function(_Rf,_Rg,_Rh){while(1){if(!E(_Rd)){if(!B(_8f(B(_Mc(_Rg,_Rc)),_Lv))){if(!B(_8f(_Rg,_c7))){var _Ri=B(_pH(_Rf,_Rf)),_Rj=B(_LX(B(_aJ(_Rg,_c7)),_Rc)),_Rk=B(_pH(_Rf,_Rh));_Rf=_Ri;_Rg=_Rj;_Rh=_Rk;continue;}else{return new F(function(){return _pH(_Rf,_Rh);});}}else{var _Ri=B(_pH(_Rf,_Rf)),_Rj=B(_LX(_Rg,_Rc));_Rf=_Ri;_Rg=_Rj;continue;}}else{return E(_8a);}}},_Rl=function(_Rm,_Rn){while(1){if(!E(_Rd)){if(!B(_8f(B(_Mc(_Rn,_Rc)),_Lv))){if(!B(_8f(_Rn,_c7))){return new F(function(){return _Re(B(_pH(_Rm,_Rm)),B(_LX(B(_aJ(_Rn,_c7)),_Rc)),_Rm);});}else{return E(_Rm);}}else{var _Ro=B(_pH(_Rm,_Rm)),_Rp=B(_LX(_Rn,_Rc));_Rm=_Ro;_Rn=_Rp;continue;}}else{return E(_8a);}}},_Rq=function(_Rr,_Rs){if(!B(_92(_Rs,_Lv))){if(!B(_8f(_Rs,_Lv))){return new F(function(){return _Rl(_Rr,_Rs);});}else{return E(_c7);}}else{return E(_OD);}},_Rt=94,_Ru=45,_Rv=43,_Rw=42,_Rx=function(_Ry,_Rz){while(1){var _RA=B((function(_RB,_RC){var _RD=E(_RC);if(!_RD._){return __Z;}else{if((B(_7a(_RB,0))+1|0)==B(_7a(_RD,0))){if(!B(_4B(_6f,_Rt,_RB))){if(!B(_4B(_6f,_Rw,_RB))){if(!B(_4B(_6f,_Rv,_RB))){if(!B(_4B(_6f,_Ru,_RB))){return E(_RD);}else{var _RE=B(_QL(_aJ,45,_RB,_RD));_Ry=_RE.a;_Rz=_RE.b;return __continue;}}else{var _RF=B(_QL(_8q,43,_RB,_RD));_Ry=_RF.a;_Rz=_RF.b;return __continue;}}else{var _RG=B(_QL(_pH,42,_RB,_RD));_Ry=_RG.a;_Rz=_RG.b;return __continue;}}else{var _RH=B(_QL(_Rq,94,new T(function(){return B(_QJ(_RB));}),new T(function(){return B(_QE(_RD,_10));})));_Ry=_RH.a;_Rz=_RH.b;return __continue;}}else{return __Z;}}})(_Ry,_Rz));if(_RA!=__continue){return _RA;}}},_RI=function(_RJ){var _RK=E(_RJ);if(!_RK._){return new T2(0,_10,_10);}else{var _RL=E(_RK.a),_RM=new T(function(){var _RN=B(_RI(_RK.b));return new T2(0,_RN.a,_RN.b);});return new T2(0,new T2(1,_RL.a,new T(function(){return E(E(_RM).a);})),new T2(1,_RL.b,new T(function(){return E(E(_RM).b);})));}},_RO=new T(function(){return B(unCStr("0123456789+-"));}),_RP=function(_RQ){while(1){var _RR=E(_RQ);if(!_RR._){return true;}else{if(!B(_4B(_6f,_RR.a,_RO))){return false;}else{_RQ=_RR.b;continue;}}}},_RS=new T(function(){return B(err(_my));}),_RT=new T(function(){return B(err(_mA));}),_RU=function(_RV,_RW){var _RX=function(_RY,_RZ){var _S0=function(_S1){return new F(function(){return A1(_RZ,new T(function(){return B(_bo(_S1));}));});},_S2=new T(function(){return B(_xr(function(_S3){return new F(function(){return A3(_RV,_S3,_RY,_S0);});}));}),_S4=function(_S5){return E(_S2);},_S6=function(_S7){return new F(function(){return A2(_w8,_S7,_S4);});},_S8=new T(function(){return B(_xr(function(_S9){var _Sa=E(_S9);if(_Sa._==4){var _Sb=E(_Sa.a);if(!_Sb._){return new F(function(){return A3(_RV,_Sa,_RY,_RZ);});}else{if(E(_Sb.a)==45){if(!E(_Sb.b)._){return E(new T1(1,_S6));}else{return new F(function(){return A3(_RV,_Sa,_RY,_RZ);});}}else{return new F(function(){return A3(_RV,_Sa,_RY,_RZ);});}}}else{return new F(function(){return A3(_RV,_Sa,_RY,_RZ);});}}));}),_Sc=function(_Sd){return E(_S8);};return new T1(1,function(_Se){return new F(function(){return A2(_w8,_Se,_Sc);});});};return new F(function(){return _yi(_RX,_RW);});},_Sf=function(_Sg){var _Sh=E(_Sg);if(_Sh._==5){var _Si=B(_yO(_Sh.a));return (_Si._==0)?E(_yT):function(_Sj,_Sk){return new F(function(){return A1(_Sk,_Si.a);});};}else{return E(_yT);}},_Sl=new T(function(){return B(A3(_RU,_Sf,_xY,_z3));}),_Sm=function(_Sn,_So){var _Sp=E(_So);if(!_Sp._){return __Z;}else{var _Sq=_Sp.a,_Sr=_Sp.b,_Ss=function(_St){var _Su=B(_RI(_Sn)),_Sv=_Su.a;return (!B(_4B(_fq,_Sq,_Sv)))?__Z:new T2(1,new T(function(){return B(_77(_Su.b,B(_iC(_fq,_Sq,_Sv))));}),new T(function(){return B(_Sm(_Sn,_Sr));}));};if(!B(_fi(_Sq,_10))){if(!B(_RP(_Sq))){return new F(function(){return _Ss(_);});}else{return new T2(1,new T(function(){var _Sw=B(_za(B(_mJ(_Sl,_Sq))));if(!_Sw._){return E(_RS);}else{if(!E(_Sw.b)._){return E(_Sw.a);}else{return E(_RT);}}}),new T(function(){return B(_Sm(_Sn,_Sr));}));}}else{return new F(function(){return _Ss(_);});}}},_Sx=function(_Sy,_Sz){while(1){var _SA=E(_Sy);if(!_SA._){return E(_Sz);}else{_Sy=_SA.b;_Sz=_SA.a;continue;}}},_SB=function(_SC,_SD,_SE){return new F(function(){return _Sx(_SD,_SC);});},_SF=function(_SG,_SH){var _SI=B(_Ql(_SH)),_SJ=B(_Rx(_SI.b,B(_Sm(_SG,_SI.a))));if(!_SJ._){return E(_SH);}else{return new F(function(){return _Ok(0,B(_SB(_SJ.a,_SJ.b,_Dm)),_10);});}},_SK=function(_SL,_SM){var _SN=function(_SO,_SP){while(1){var _SQ=B((function(_SR,_SS){var _ST=E(_SS);if(!_ST._){return (!B(_hb(_SR,_10)))?new T2(0,_kr,_SR):new T2(0,_qO,_10);}else{var _SU=_ST.b,_SV=B(_Pq(_ST.a)).a;if(!B(_4B(_6f,_Pz,_SV))){var _SW=_SR;_SO=_SW;_SP=_SU;return __continue;}else{var _SX=B(_Q5(_SV)),_SY=_SX.a,_SZ=_SX.b;if(!B(_hb(B(_SF(_SL,_SY)),B(_SF(_SL,_SZ))))){return new T2(0,_qO,_10);}else{if(!B(_fi(_SZ,_10))){var _T0=new T(function(){if(!B(_hb(_SR,_10))){return B(_y(_SR,new T(function(){return B(unAppCStr(" ",_SY));},1)));}else{return E(_SY);}});_SO=_T0;_SP=_SU;return __continue;}else{return new T2(0,_qO,_10);}}}}})(_SO,_SP));if(_SQ!=__continue){return _SQ;}}};return new F(function(){return _SN(_10,_SM);});},_T1=function(_T2,_T3){while(1){var _T4=E(_T2);if(!_T4._){return E(_T3);}else{_T2=_T4.b;_T3=_T4.a;continue;}}},_T5=function(_T6,_T7,_T8){return new F(function(){return _T1(_T7,_T6);});},_T9=function(_Ta,_Tb){while(1){var _Tc=E(_Ta);if(!_Tc._){return E(_Tb);}else{_Ta=_Tc.b;_Tb=_Tc.a;continue;}}},_Td=function(_Te,_Tf,_Tg){return new F(function(){return _T9(_Tf,_Te);});},_Th=function(_Ti,_Tj){while(1){var _Tk=E(_Tj);if(!_Tk._){return __Z;}else{var _Tl=_Tk.b,_Tm=E(_Ti);if(_Tm==1){return E(_Tl);}else{_Ti=_Tm-1|0;_Tj=_Tl;continue;}}}},_Tn=function(_To,_Tp){var _Tq=new T(function(){var _Tr=_To+1|0;if(_Tr>0){return B(_Th(_Tr,_Tp));}else{return E(_Tp);}});if(0>=_To){return E(_Tq);}else{var _Ts=function(_Tt,_Tu){var _Tv=E(_Tt);if(!_Tv._){return E(_Tq);}else{var _Tw=_Tv.a,_Tx=E(_Tu);return (_Tx==1)?new T2(1,_Tw,_Tq):new T2(1,_Tw,new T(function(){return B(_Ts(_Tv.b,_Tx-1|0));}));}};return new F(function(){return _Ts(_Tp,_To);});}},_Ty=new T(function(){return B(A3(_yt,_yW,_xY,_z3));}),_Tz=new T(function(){return B(unCStr("!"));}),_TA=0,_TB=function(_TC){return new F(function(){return _kt("Check.hs:156:7-35|(co : na : xs)");});},_TD=new T(function(){return B(_TB(_));}),_TE=new T(function(){return B(err(_mA));}),_TF=new T(function(){return B(err(_my));}),_TG=new T(function(){return B(unCStr(":"));}),_TH=function(_TI){var _TJ=E(_TI);if(!_TJ._){return __Z;}else{var _TK=new T(function(){return B(_y(_TG,new T(function(){return B(_TH(_TJ.b));},1)));},1);return new F(function(){return _y(_TJ.a,_TK);});}},_TL=function(_TM,_TN){var _TO=new T(function(){return B(_y(_TG,new T(function(){return B(_TH(_TN));},1)));},1);return new F(function(){return _y(_TM,_TO);});},_TP=function(_TQ,_TR){var _TS=E(_TR);if(!_TS._){return E(_TD);}else{var _TT=E(_TS.b);if(!_TT._){return E(_TD);}else{var _TU=E(_TS.a),_TV=new T(function(){var _TW=B(_ky(58,_TT.a,_TT.b));return new T2(0,_TW.a,_TW.b);}),_TX=function(_TY,_TZ,_U0){var _U1=function(_U2){if((_TQ+1|0)!=_U2){return new T3(0,_TQ+1|0,_TZ,_TS);}else{var _U3=E(_U0);return (_U3._==0)?new T3(0,_TA,_TZ,_10):new T3(0,_TA,_TZ,new T(function(){var _U4=B(_TL(_U3.a,_U3.b));if(!_U4._){return E(_Bf);}else{return B(_Ba(_U4.a,_U4.b));}}));}};if(!B(_hb(_TY,_Tz))){var _U5=B(_za(B(_mJ(_Ty,_TY))));if(!_U5._){return E(_TF);}else{if(!E(_U5.b)._){return new F(function(){return _U1(E(_U5.a));});}else{return E(_TE);}}}else{return new F(function(){return _U1( -1);});}};if(E(_TU)==58){return new F(function(){return _TX(_10,new T(function(){return E(E(_TV).a);}),new T(function(){return E(E(_TV).b);}));});}else{var _U6=E(_TV),_U7=E(_U6.b);if(!_U7._){return E(_TD);}else{return new F(function(){return _TX(new T2(1,_TU,_U6.a),_U7.a,_U7.b);});}}}}},_U8=function(_U9,_Ua){while(1){var _Ub=E(_Ua);if(!_Ub._){return __Z;}else{var _Uc=_Ub.b,_Ud=E(_U9);if(_Ud==1){return E(_Uc);}else{_U9=_Ud-1|0;_Ua=_Uc;continue;}}}},_Ue=function(_Uf,_Ug,_Uh){var _Ui=new T2(1,_Ug,new T(function(){var _Uj=_Uf+1|0;if(_Uj>0){return B(_U8(_Uj,_Uh));}else{return E(_Uh);}}));if(0>=_Uf){return E(_Ui);}else{var _Uk=function(_Ul,_Um){var _Un=E(_Ul);if(!_Un._){return E(_Ui);}else{var _Uo=_Un.a,_Up=E(_Um);return (_Up==1)?new T2(1,_Uo,_Ui):new T2(1,_Uo,new T(function(){return B(_Uk(_Un.b,_Up-1|0));}));}};return new F(function(){return _Uk(_Uh,_Uf);});}},_Uq=function(_Ur,_Us){if(_Ur<=_Us){var _Ut=function(_Uu){return new T2(1,_Uu,new T(function(){if(_Uu!=_Us){return B(_Ut(_Uu+1|0));}else{return __Z;}}));};return new F(function(){return _Ut(_Ur);});}else{return __Z;}},_Uv=new T2(0,_AS,_AQ),_Uw=function(_Ux,_Uy,_Uz){while(1){var _UA=E(_Uz);if(!_UA._){return E(_Uv);}else{var _UB=_UA.b,_UC=E(_UA.a),_UD=E(_UC.a);if(_Ux!=E(_UD.a)){_Uz=_UB;continue;}else{if(_Uy!=E(_UD.b)){_Uz=_UB;continue;}else{return E(_UC.b);}}}}},_UE=function(_UF,_UG){while(1){var _UH=E(_UG);if(!_UH._){return __Z;}else{var _UI=_UH.b,_UJ=E(_UF);if(_UJ==1){return E(_UI);}else{_UF=_UJ-1|0;_UG=_UI;continue;}}}},_UK=function(_UL,_UM,_UN){var _UO=E(_UL);if(_UO==1){return E(_UN);}else{return new F(function(){return _UE(_UO-1|0,_UN);});}},_UP=function(_UQ,_UR,_US){return new T2(1,new T(function(){if(0>=_UQ){return __Z;}else{return B(_eI(_UQ,new T2(1,_UR,_US)));}}),new T(function(){if(_UQ>0){return B(_UT(_UQ,B(_UK(_UQ,_UR,_US))));}else{return B(_UP(_UQ,_UR,_US));}}));},_UT=function(_UU,_UV){var _UW=E(_UV);if(!_UW._){return __Z;}else{var _UX=_UW.a,_UY=_UW.b;return new T2(1,new T(function(){if(0>=_UU){return __Z;}else{return B(_eI(_UU,_UW));}}),new T(function(){if(_UU>0){return B(_UT(_UU,B(_UK(_UU,_UX,_UY))));}else{return B(_UP(_UU,_UX,_UY));}}));}},_UZ=function(_V0,_V1,_V2){var _V3=_V1-1|0;if(0<=_V3){var _V4=E(_V0),_V5=function(_V6){var _V7=new T(function(){if(_V6!=_V3){return B(_V5(_V6+1|0));}else{return __Z;}}),_V8=function(_V9){var _Va=E(_V9);return (_Va._==0)?E(_V7):new T2(1,new T(function(){var _Vb=E(_V2);if(!_Vb._){return E(_Uv);}else{var _Vc=_Vb.b,_Vd=E(_Vb.a),_Ve=E(_Vd.a),_Vf=E(_Va.a);if(_Vf!=E(_Ve.a)){return B(_Uw(_Vf,_V6,_Vc));}else{if(_V6!=E(_Ve.b)){return B(_Uw(_Vf,_V6,_Vc));}else{return E(_Vd.b);}}}}),new T(function(){return B(_V8(_Va.b));}));};return new F(function(){return _V8(B(_Uq(0,_V4-1|0)));});};return new F(function(){return _UT(_V4,B(_V5(0)));});}else{return __Z;}},_Vg=function(_Vh,_Vi){while(1){var _Vj=E(_Vi);if(!_Vj._){return __Z;}else{var _Vk=_Vj.b,_Vl=E(_Vh);if(_Vl==1){return E(_Vk);}else{_Vh=_Vl-1|0;_Vi=_Vk;continue;}}}},_Vm=function(_Vn){var _Vo=E(_Vn);if(!_Vo._){return new T2(0,_10,_10);}else{var _Vp=E(_Vo.a),_Vq=new T(function(){var _Vr=B(_Vm(_Vo.b));return new T2(0,_Vr.a,_Vr.b);});return new T2(0,new T2(1,_Vp.a,new T(function(){return E(E(_Vq).a);})),new T2(1,_Vp.b,new T(function(){return E(E(_Vq).b);})));}},_Vs=function(_Vt,_Vu,_Vv){var _Vw=new T(function(){var _Vx=B(_Vm(_Vv));return new T2(0,_Vx.a,_Vx.b);});return new T2(0,new T2(1,_Vt,new T(function(){return E(E(_Vw).a);})),new T2(1,_Vu,new T(function(){return E(E(_Vw).b);})));},_Vy=new T(function(){return B(unCStr("\u4e0d\u601d\u8b70\u306a\u3068\u3053\u308d\u30fb\u30fb\u30fb\u3002\n\u3053\u3053\u306f \u3069\u3053\u3060\u3089\u3046\u30fb\u30fb\u30fb\u3002\n\uff1c\u30ad\u30fc\u30dc\u30fc\u30c9\u306a\u3089 hjkl\u30ad\u30fc\u3092\u3002\n\u30bf\u30c3\u30c1\u306a\u3089 \u753b\u9762\u306e\u7aef\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3053\u3068\u3067 \u52d5\u3051\u3055\u3046\u3067\u3059\uff1e{e.bC.m1:s0C0:1:s0C1:1:s0C2:0:s0C3}{e.==.m1:s0c}{e.b9.m1:s090}{e.b8.m1:s080}{e.b3.m1:s030}{e.b2.m1:s020}"));}),_Vz=new T(function(){return B(unCStr("s0C0"));}),_VA=new T(function(){return B(unCStr("\n\u300c\u3084\u3042\u3002\n\u308f\u3042\uff01 \u306a\u3093\u304b\u6587\u5b57\u304c\u3057\u3083\u3079\u3063\u305f\uff01\u3002\n\u300c\u6587\u5b57\u3062\u3083\u306a\u3044\u3088\u3002\n\u300c\u50d5\u306f \u306d\u3053\u3060\u3088\u3002\n\u3044\u3084 \u306d\u3053\u3082 \u666e\u901a\u3057\u3083\u3079\u3089\u306a\u3044\u3057\u3002\n\u300c\u3069\u3046\u3060\u3044\uff1f \u6b21\u306b\u9032\u3081\u3055\u3046\u304b\u3044\uff1f\u3002\n\u6b21\u3063\u3066\u3044\u3063\u3066\u3082 \u3088\u304f\u308f\u304b\u3089\u306a\u3044\u3051\u3069\u30fb\u30fb\u30fb\u3002\n\u307e\u3042 \u81ea\u5206\u3067\u4f55\u3068\u304b\u3084\u3063\u3066\u307f\u308b\u3088\u3002\n\u300c\u3075\u3045\u301c\u3093\u3002\u307e\u3042 \u3044\u3044\u3084\u3002\n\u300c\u50d5\u306e\u52a9\u3051\u304c\u5fc5\u8981\u306a\u3089 \u8a00\u3063\u3066\u306d\u3002\n\u30fb\u30fb\u30fb\u30fb\u3002{ct.1.Fr}{ct.2.Fr}{ct.3.Fr}{ct.7.Fr}{ct.8.Fr}{ct.9.Fr}"));}),_VB=new T2(0,_Vz,_VA),_VC=new T(function(){return B(unCStr("s0C1"));}),_VD=new T(function(){return B(unCStr("\n\u300c\u3053\u306e\u4e16\u754c\u306b\u306f \u6301\u3066\u308b\u30e2\u30ce\u3002 \u6301\u3066\u306a\u3044\u30e2\u30ce\u3002 \u52d5\u304b\u305b\u308b\u30e2\u30ce\u3002 \u52d5\u304b\u306a\u3044\u30e2\u30ce \u3068\u304b\u304c \u3042\u308b\u3088\u3002\n\u300c\u6301\u3063\u305f\u3082\u306e\u3092 \u81ea\u5206\u306e\u3090\u308b\u6240\u306b\u7f6e\u304f\u5834\u5408\u306f \u30ad\u30fc\u30dc\u30fc\u30c9\u306a\u3089 \u30b9\u30da\u30fc\u30b9\u30ad\u30fc\u3002\n\u300c\u30bf\u30c3\u30c1\u306a\u3089 \u307e\u3093\u306a\u304b\u908a\uff1a\u3078\u3093\uff1a\u3092\u30bf\u30c3\u30d7 \u304b\u306a\u3002"));}),_VE=new T2(0,_VC,_VD),_VF=new T(function(){return B(unCStr("s0C2"));}),_VG=new T(function(){return B(unCStr("\n\u300c\u4e00\u756a\u4e0a\u306e\u884c\u306b =\uff1c\u30a4\u30b3\u30fc\u30eb\uff1e \u304c\u3042\u308b\u3067\u3057\u3087\uff1f\u3002\n\u300c\u30a4\u30b3\u30fc\u30eb \u306f \u305d\u306e\u5de6\u3068 \u53f3\u304c \u7b49\u3057\u3044 \u3063\u3066\u3053\u3068\u3060\u3088\u3002\n\u300c\u30a4\u30b3\u30fc\u30eb \u306e\u5de6\u3068\u53f3\u3092\u7b49\u3057\u304f\u3057\u3066\u3042\u3052\u308c\u3070 \u304d\u3063\u3068\u524d\u306b\u9032\u3081\u308b\u306f\u305a\u3060\u3088\u3002"));}),_VH=new T2(0,_VF,_VG),_VI=new T(function(){return B(unCStr("s0C3"));}),_VJ=new T(function(){return B(unCStr("\n\u300c\u4e0a\u306e\u7b49\u5f0f\u3092\u5b8c\u6210\u3055\u305b\u3084\u3046"));}),_VK=new T2(0,_VI,_VJ),_VL=new T(function(){return B(unCStr("s0c"));}),_VM=new T(function(){return B(unCStr("\n\u300c\u30aa\u30c3\u30b1\u30fc\uff01 \u7c21\uff1a\u304b\u3093\uff1a\u55ae\uff1a\u305f\u3093\uff1a\u3060\u3063\u305f\uff1f\u3002{d.bC}{e.bC.m0:s0C4}\n\u300c\u305d\u308c\u3062\u3083\u3042 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u90e8\uff1a\u3078\uff1a\u5c4b\uff1a\u3084\uff1a\u3078\u3044\u3053\u3063\u304b{p.2,4.n,Ex}{e.un.l}{e.c0.m1:s1}"));}),_VN=new T2(0,_VL,_VM),_VO=new T(function(){return B(unCStr("s0C4"));}),_VP=new T(function(){return B(unCStr("\n\u300c\u6b21\u306e\u90e8\u5c4b\u3078 \u3044\u304b\u3046\u3088"));}),_VQ=new T2(0,_VO,_VP),_VR=new T(function(){return B(unCStr("s1"));}),_VS=new T(function(){return B(unCStr("\n\u3042\u308c\uff1f\u3069\u3053\u884c\u3063\u305f\uff1f\u3002\n\u300c\u307c\u304f\u306e\u3053\u3068\u3092 \u6c23\u306b\u304b\u3051\u3066\u304f\u308c\u308b\u3093\u3060\u3002 \u3042\u308a\u304c\u305f\u3046\uff01\u3002\n\u300c\u3061\u3087\u3063\u3068\u3053\u3053\u306b\u306f \u5c45\uff1a\u3090\uff1a\u306a\u3044\u3051\u3069 \u8a00\u8449\u306f\u805e\u3053\u3078\u3066\u308b\u3067\u3057\u3087\uff1f\u3002\n\u300c\u4f55\u304b\u3042\u3063\u305f\u3089 \u307e\u305f\u7e4b\uff1a\u3064\u306a\uff1a\u304c\u308b\u304b\u3089 \u5927\u4e08\u592b\u3060\u3088\u301c\u3002\n\u3064\u306a\u304c\u308b\uff1f\u3002 \u307e\u3042\u3044\u3044\u3084\u3002\n\u3066\u304b \u3053\u3053\u306f\u4f55\u3060\uff1f{d.bC}{e.b=0.m0:s1Q1}{e.b=1.m0:s1Q2}{e.b=2.m0:s1Q3}{e.bS.m1:s1S0}{e.vC.m1:s1C0}{e.bJ.m1:s1J0:1:s1J1}{e.uR.r}{e.==.m1:s1c}"));}),_VT=new T2(0,_VR,_VS),_VU=new T(function(){return B(unCStr("s1Q1"));}),_VV=new T(function(){return B(unCStr("\n\u6e29\u5ba4\u52b9\u679c\u306e\u6bd4\u8f03\u7684\u9ad8\u3044\u30ac\u30b9\u306f\uff1f"));}),_VW=new T2(0,_VU,_VV),_VX=new T(function(){return B(unCStr("s1Q3"));}),_VY=new T(function(){return B(unCStr("\n\u4e8c\u9178\u5316\u70ad\u7d20\u306e\u5927\u6c23\u4e2d\u306e\u5272\u5408\u306f\uff1f"));}),_VZ=new T2(0,_VX,_VY),_W0=new T(function(){return B(unCStr("s020"));}),_W1=new T(function(){return B(unCStr("\n\u300c\u3072\u3068\u3064\u3057\u304b\u306a\u3044\u4e16\u754c\u306e\u4e2d\u306b \u3042\u306a\u305f\u304c\u751f\u304d\u3066\u3090\u308b\u3068\u3044\u3075\u306e\u306f \u5be6\uff1a\u3058\u3064\uff1a\u306f \u3072\u3068\u3064\u306e\u89c0\uff1a\u304b\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u3067\u3042\u308b\u3002\n\u300c\u89c0\u5ff5\u3068\u3044\u3075\u306e\u306f \u3042\u306a\u305f\u306e\u5fc3\u304c\u6c7a\u3081\u3066\u3090\u308b \u4fe1\u3058\u3066\u3090\u308b\u3053\u3068\u304c\u3089\u3067\u3042\u308b\u3002\n\u300c\u305d\u308c\u306f \u3042\u306a\u305f\u306e\u5fc3\u306e\u4e2d\u306b\u3042\u308b \u7b49\uff1a\u3068\u3046\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u3067\u3042\u308b\u3002\n\u300c\u305b\u304b\u3044\u306f \u3072\u3068\u3064 \u305b\u304b\u3044\u306f \u304a\u306a\u3058 \u305b\u304b\u3044\u306f \u307e\u308b\u3044 \u305f\u3060\u3072\u3068\u3064\u3002\n\u300c\u3053\u308c\u306f \u3059\u3079\u3066 \u3042\u306a\u305f\u306e\u5fc3\u306e\u4e2d\u306b\u3042\u308b \u7b49\u5f0f \u3064\u307e\u308a \u89c0\u5ff5\u3067\u3042\u308b\u3002\n\u300c\u305d\u306e\u89c0\u5ff5\u3092 \u6301\u3061\u7e8c\uff1a\u3064\u3065\uff1a\u3051\u308b\u81ea\u7531\u3082 \u305d\u306e\u89c0\u5ff5\u3092 \u5225\u306e\u3082\u306e\u306b\u8b8a\uff1a\u304b\uff1a\u3078\u308b\u81ea\uff1a\u3058\uff1a\u7531\uff1a\u3044\u3046\uff1a\u3082 \u3042\u306a\u305f\u306f\u6301\u3063\u3066\u3090\u308b\u3002"));}),_W2=new T2(0,_W0,_W1),_W3=new T2(1,_W2,_10),_W4=new T(function(){return B(unCStr("s030"));}),_W5=new T(function(){return B(unCStr("\n\u300c\u73fe\uff1a\u3052\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u306e\u793e\uff1a\u3057\u3083\uff1a\u6703\uff1a\u304b\u3044\uff1a\u3067 \u6700\u3082\u96e3\uff1a\u3080\u3065\u304b\uff1a\u3057\u3044\u3053\u3068\u306f \u3059\u3079\u3066\u304c\u7c21\uff1a\u304b\u3093\uff1a\u55ae\uff1a\u305f\u3093\uff1a\u3067\u3042\u308b\u3053\u3068\u3092 \u7406\uff1a\u308a\uff1a\u89e3\uff1a\u304b\u3044\uff1a\u3059\u308b\u3053\u3068\u3067\u3042\u308b\u3002\n\u300c\u3053\u306e\u4e16\u754c\u306e\u6cd5\uff1a\u306f\u3075\uff1a\u5247\uff1a\u305d\u304f\uff1a \u30eb\u30fc\u30eb\u306f \u975e\uff1a\u3072\uff1a\u5e38\uff1a\u3058\u3083\u3046\uff1a\u306b\u7c21\u55ae\u3067 \u3072\u3068\u3064\u3057\u304b\u306a\u3044\u3002\n\u300c\u305d\u308c\u306f \u8207\uff1a\u3042\u305f\uff1a\u3078\u305f\u3082\u306e\u304c \u8fd4\u3063\u3066\u304f\u308b \u3068\u3044\u3075\u6cd5\u5247 \u305f\u3060\u3072\u3068\u3064\u3067\u3042\u308b\u3002\n\u300c\u3057\u3044\u3066 \u307e\u3046\u3072\u3068\u3064 \u3042\u308b\u3068\u3059\u308c\u3070\u3002\n\u300c\u3042\u306a\u305f\u306f \u5b58\uff1a\u305d\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u3057\u3066\u3090\u308b \u3068\u3044\u3075\u3053\u3068\u3060\u3002"));}),_W6=new T2(0,_W4,_W5),_W7=new T2(1,_W6,_W3),_W8=new T(function(){return B(unCStr("s080"));}),_W9=new T(function(){return B(unCStr("\n\u300c\u8089\uff1a\u306b\u304f\uff1a\u9ad4\uff1a\u305f\u3044\uff1a\u304c\u3042\u308b\u304b\u3089\u7cbe\uff1a\u305b\u3044\uff1a\u795e\uff1a\u3057\u3093\uff1a\u304c\u3042\u308b \u3068\u3044\u3075\u306e\u306f \u305d\u308c\u3092\u6b63\u3057\u3044\u3068\u3042\u306a\u305f\u304c\u6c7a\u3081\u305f\u306e\u3067\u3042\u308c\u3070 \u6b63\u3057\u3044\u3002\n\u300c\u7cbe\u795e\u304c\u3042\u308b\u304b\u3089 \u8089\u9ad4\u304c\u3042\u308b \u3068\u3044\u3075\u306e\u306f \u6b63\u3057\u3044\u3002\n\u300c\u305d\u306e\u3053\u3068\u304b\u3089\u306e\u307f \u8089\u9ad4\u304c\u3042\u308b\u304b\u3089\u7cbe\u795e\u304c\u3042\u308b \u3068\u3044\u3075\u8003\u3078\u3092\u80af\uff1a\u3053\u3046\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3059\u308b\u3053\u3068\u304c\u3067\u304d\u308b\u3002\n\u300c\u306a\u305c\u306a\u3089 \u7cbe\u795e\u3092\u5148 \u3068\u3059\u308b\u306e\u3067\u3042\u308c\u3070 \u3042\u306a\u305f\u306e\u89c0\uff1a\u304b\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u304c \u6b63\u3057\u3055\u306e\u57fa\uff1a\u3082\u3068\uff1a\u3092\u306a\u3057\u3066\u3090\u308b\u304b\u3089\u3067\u3042\u308b\u3002\n\u300c\u7cbe\u795e\u304c\u8089\u9ad4\u306e\u524d\u306b\u3042\u308b \u3068\u3044\u3075\u3053\u3068\u306b\u3088\u3063\u3066\u306e\u307f \u8089\u9ad4\u304c\u524d\u3067\u3042\u3063\u3066\u3082\u3088\u3044\u3057 \u7cbe\u795e\u304c\u524d\u3067\u3042\u3063\u3066\u3082\u3088\u3044 \u3068\u3044\u3075\u81ea\u7531\u304c\u751f\u3058\u308b\u3002\n\u300c\u3069\u3061\u3089\u3067\u3082 \u3042\u306a\u305f\u306e\u597d\u304d\u306a\u3084\u3046\u306b \u9078\u3093\u3067\u3088\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306a\u308b\u3002"));}),_Wa=new T2(0,_W8,_W9),_Wb=new T2(1,_Wa,_W7),_Wc=new T(function(){return B(unCStr("s090"));}),_Wd=new T(function(){return B(unCStr("\n\u300c\u89c0\uff1a\u304b\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u304c\u611f\uff1a\u304b\u3093\uff1a\u60c5\uff1a\u3058\u3084\u3046\uff1a\u3092\u751f\u307f \u611f\u60c5\u304c\u884c\uff1a\u304b\u3046\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3092\u4fc3\uff1a\u3046\u306a\u304c\uff1a\u3059\u3002\n\u300c\u3042\u306a\u305f\u306e\u4e16\u754c\u306f \u3042\u306a\u305f\u306e\u89c0\u5ff5\u306b\u3088\u3063\u3066 \u6587\u5b57\u901a\u308a \u5275\uff1a\u3055\u3046\uff1a\u9020\uff1a\u3056\u3046\uff1a\u3055\u308c\u3066\u3090\u308b\u3002\n\u300c\u305d\u306e\u3053\u3068\u3092\u5fd8\uff1a\u308f\u3059\uff1a\u308c\u308b\u3068\u3044\u3075\u306e\u3082 \u3042\u306a\u305f\u304c\u671b\uff1a\u306e\u305e\uff1a\u307f \u5275\uff1a\u3064\u304f\uff1a\u308a\u51fa\u3057\u305f\u3053\u3068\u3002\n\u300c\u89c0\u5ff5\u306f \u3042\u306a\u305f\u306e\u610f\uff1a\u3044\uff1a\u601d\uff1a\u3057\uff1a\u306b\u3088\u3063\u3066 \u8b8a\uff1a\u304b\uff1a\u3048\u308b\u3053\u3068\u304c\u3067\u304d\u308b\u3002\n\u300c\u89c0\u5ff5\u304c\u4e16\u754c\u3092\u5275\u9020\u3057\u3066\u3090\u308b \u3068\u3044\u3075\u3053\u3068\u306f \u3042\u306a\u305f\u306e\u610f\u601d\u304c \u4e16\u754c\u3092\u5275\u9020\u3067\u304d\u308b \u3068\u3044\u3075\u3053\u3068\u3002\n\u300c\u3042\u306a\u305f\u306e\u5468\uff1a\u3057\u3046\uff1a\u56f2\uff1a\u3090\uff1a\u306e \u3059\u3079\u3066\u306e\u72b6\uff1a\u3058\u3083\u3046\uff1a\u6cc1\uff1a\u304d\u3083\u3046\uff1a\u3092 \u3042\u306a\u305f\u304c \u30b3\u30f3\u30c8\u30ed\u30fc\u30eb\u3067\u304d\u308b \u3068\u3044\u3075\u3053\u3068\u3002\n\u300c\u305d\u308c\u3092\u5be6\uff1a\u3058\u3064\uff1a\u884c\uff1a\u304b\u3046\uff1a\u3059\u308b\u3082 \u3057\u306a\u3044\u3082 \u3059\u3079\u3066 \u3042\u306a\u305f\u3060\u3051\u306e\u610f\u601d\u306b\u59d4\uff1a\u3086\u3060\uff1a\u306d\u3089\u308c\u3066\u3090\u308b\u3002"));}),_We=new T2(0,_Wc,_Wd),_Wf=new T2(1,_We,_Wb),_Wg=new T(function(){return B(unCStr("nubatama"));}),_Wh=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_Wi=new T2(0,_Wg,_Wh),_Wj=new T2(1,_Wi,_Wf),_Wk=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_Wl=new T(function(){return B(unCStr("msgW"));}),_Wm=new T2(0,_Wl,_Wk),_Wn=new T2(1,_Wm,_Wj),_Wo=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u307e\u305b\u3046"));}),_Wp=new T(function(){return B(unCStr("msgR"));}),_Wq=new T2(0,_Wp,_Wo),_Wr=new T2(1,_Wq,_Wn),_Ws=new T(function(){return B(unCStr("s2c"));}),_Wt=new T(function(){return B(unCStr("\n\u300c\u3059\u3054\u3044\u306d\uff01 \u30af\u30ea\u30a2\u3060\u3088\uff01\u3002{da}"));}),_Wu=new T2(0,_Ws,_Wt),_Wv=new T2(1,_Wu,_Wr),_Ww=new T(function(){return B(unCStr("s2_3"));}),_Wx=new T(function(){return B(unCStr("\n\u300c\u3075\u3064\u3046\u30fb\u30fb\u30fb\u3067\u3059\u304b\u30fc\u3002\n\u306a\u306b\u304b\uff1f\u3002\n\u300c\u3044\u3084 \u3079\u3064\u306b \u305d\u308c\u306f\u305d\u308c\u3067 \u3044\u3044\u3093\u3060\u3051\u3069\u306d\u30fc\u3002\n\u300c\u30fb\u30fb\u30fb\u306a\u3093\u304b\u304b\u3046 \u3075\u3064\u3046 \u3063\u3066 \u307b\u3093\u3068\u306f\u30a4\u30e4\u306a\u3093\u3060\u3051\u3069 \u305d\u308c\u8a00\u3072\u305f\u304f\u306a\u3044\u3068\u304d\u306b\u4f7f\u3075\u3084\u3046\u306a\u30a4\u30e1\u30fc\u30b8\u304c\u30fb\u30fb\u3002\n\u3044\u3084 \u55ae\u7d14\u306b\u8208\u5473\u306a\u3044\u3060\u3051\u3060\u304b\u3089\u3002\n\u5acc\u3072\u3067\u3082\u306a\u3044\u3057 \u597d\u304d\u3067\u3082\u306a\u3044\u3002\n\u300c\u3075\u30fc\u3093 \u305d\u3063\u304b\u30fc\u30fb\u30fb\u30fb\u3002\n\u306a\u3093\u3060\u3088\u3002\n\u300c\u307c\u304f\u3061\u3093 \u304b\u308f\u3044\u3044\u3074\u3087\u3093\uff01\u3002\n\u306f\u3044\uff1f"));}),_Wy=new T2(0,_Ww,_Wx),_Wz=new T2(1,_Wy,_Wv),_WA=new T(function(){return B(unCStr("s2_2"));}),_WB=new T(function(){return B(unCStr("\n\u300c\u305d\u3063\u304b\u30fc \u305d\u308a\u3083\u6b98\u5ff5\u3002\n\u300c\u307e\u3042 \u30d2\u30c8\u305d\u308c\u305e\u308c\u597d\u307f\u304c\u9055\u3075\u3057 \u4ed5\u65b9\u306a\u3044\u304b\u30fc\u3002\n\u3042\u304b\u3089\u3055\u307e\u306b\u6b98\u5ff5\u3055\u3046\u3060\u306d\u3002\n\u300c\u307e\u3042 \u5acc\u306f\u308c\u308b\u306e\u306f \u597d\u304d\u3062\u3083\u306a\u3044\u3057\u306d\u30fb\u30fb\u30fb\u3002\n\u3079\u3064\u306b \u304a\u524d\u304c\u7279\u5225\u5acc\u3072\u3063\u3066\u3053\u3068\u3067\u3082\u306a\u3044\u3088\u3002\n\u300c\u3055\u3046\u306a\u306e\uff01 \u3084\u3063\u305f\u30fc\uff01\u3002\n\u306a\u3093\u304b\u958b\u304d\u306a\u307b\u308b\u306e\u65e9\u3044\u306a\u30fb\u30fb\u30fb"));}),_WC=new T2(0,_WA,_WB),_WD=new T2(1,_WC,_Wz),_WE=new T(function(){return B(unCStr("s2_1"));}),_WF=new T(function(){return B(unCStr("\n\u300c\u3055\u3046\u306a\u3093\u3060\uff01\u3002\n\u300c\u3046\u308c\u3057\u3044\u306a\u3002\n\u3044\u3084 \u3079\u3064\u306b\u4e00\u822c\u7684\u306b \u3068\u3044\u3075\u3060\u3051\u3067 \u7279\u5225\u304a\u524d\u306e\u3053\u3068\u304c \u3063\u3066\u308f\u3051\u3067\u3082\u306a\u3044\u3093\u3060\u30b1\u30c9\u3002\n\u300c\u305d\u308c\u3067\u3082\u3046\u308c\u3057\u3044\u3088\u3002\n\u300c\u30cd\u30b3\u306f\u306d \u901a\u5e38\u4eba\u9593\u304c\u611f\u3058\u3066\u3090\u306a\u3044\u4e16\u754c\u3092\u898b\u3066\u3090\u308b\u3093\u3060\u3002\n\u305d\u308a\u3083 \u4eba\u9593\u3068\u9055\u3075\u52d5\u7269\u306a\u3093\u3060\u304b\u3089 \u3055\u3046\u3044\u3075\u3082\u3093\u3060\u308d\uff1f\u3002\n\u300c\u307e\u3042 \u3055\u3046\u3060\u3051\u3069 \u305d\u306e\u4e16\u754c\u306f \u3068\u3063\u3066\u3082\u30d2\u30c8\u306b\u3068\u3063\u3066\u5927\u4e8b\u306a\u3093\u3060\u3088\u3002\n\u3075\u30fc\u3093\u3002\n\u300c\u3042 \u306a\u3093\u304b\u5168\u7136\u8208\u5473\u306a\u3044\u8a00\u3072\u65b9\u30fb\u30fb\u30fb\n\u307e\u3042\u306d\u3002\n\u300c\u3075\u3093\uff01 \u3044\u3044\u3088\uff01 \u304d\u3063\u3068\u305d\u306e\u3046\u3061\u6c23\u306b\u306a\u3063\u3066\u4ed5\u65b9\u306a\u304f\u306a\u308b\u3093\u3060\u304b\u3089\u301c\u3002"));}),_WG=new T2(0,_WE,_WF),_WH=new T2(1,_WG,_WD),_WI=new T(function(){return B(unCStr("s2B0"));}),_WJ=new T(function(){return B(unCStr("\n\u300c\u304a\u306f\u3084\u3046\u3054\u3056\u3044\u307e\u3059"));}),_WK=new T2(0,_WI,_WJ),_WL=new T2(1,_WK,_WH),_WM=new T(function(){return B(unCStr("s2J0"));}),_WN=new T(function(){return B(unCStr("\n\u300c\u3053\u3093\u306b\u3061\u306f\uff01"));}),_WO=new T2(0,_WM,_WN),_WP=new T2(1,_WO,_WL),_WQ=new T(function(){return B(unCStr("s2Not"));}),_WR=new T(function(){return B(unCStr("\nNOT"));}),_WS=new T2(0,_WQ,_WR),_WT=new T2(1,_WS,_WP),_WU=new T(function(){return B(unCStr("s2N"));}),_WV=new T(function(){return B(unCStr("\n\u5fc5\u9808\u306a\u3053\u3068\u3060"));}),_WW=new T2(0,_WU,_WV),_WX=new T2(1,_WW,_WT),_WY=new T(function(){return B(unCStr("s2H"));}),_WZ=new T(function(){return B(unCStr("\n\u6709\u5bb3\u3067\u5371\u967a\u3060"));}),_X0=new T2(0,_WY,_WZ),_X1=new T2(1,_X0,_WX),_X2=new T(function(){return B(unCStr("s2I"));}),_X3=new T(function(){return B(unCStr("\n\u611f\u67d3\u3057\u305f\u3068\u3044\u3075\u3053\u3068"));}),_X4=new T2(0,_X2,_X3),_X5=new T2(1,_X4,_X1),_X6=new T(function(){return B(unCStr("s2P"));}),_X7=new T(function(){return B(unCStr("\n\u5b58\u5728\u3057\u3066\u3090\u308b"));}),_X8=new T2(0,_X6,_X7),_X9=new T2(1,_X8,_X5),_Xa=new T(function(){return B(unCStr("s2Q5"));}),_Xb=new T(function(){return B(unCStr("\n\u4eba\u3068\u63a5\u89e6\u3059\u308b\u306e\u306f"));}),_Xc=new T2(0,_Xa,_Xb),_Xd=new T2(1,_Xc,_X9),_Xe=new T(function(){return B(unCStr("s2Q4"));}),_Xf=new T(function(){return B(unCStr("\n\u30ef\u30af\u30c1\u30f3\u3092\u6253\u3064\u306e\u306f"));}),_Xg=new T2(0,_Xe,_Xf),_Xh=new T2(1,_Xg,_Xd),_Xi=new T(function(){return B(unCStr("s2Q3"));}),_Xj=new T(function(){return B(unCStr("\n\u30de\u30b9\u30af\u3092\u3059\u308b\u306e\u306f"));}),_Xk=new T2(0,_Xi,_Xj),_Xl=new T2(1,_Xk,_Xh),_Xm=new T(function(){return B(unCStr("s2Q2"));}),_Xn=new T(function(){return B(unCStr("\nPCR\u691c\u67fb\u3092\u3057\u3066\u967d\u6027\u306b\u306a\u308b\u3068\u3044\u3075\u3053\u3068\u306f"));}),_Xo=new T2(0,_Xm,_Xn),_Xp=new T2(1,_Xo,_Xl),_Xq=new T(function(){return B(unCStr("s2Q1"));}),_Xr=new T(function(){return B(unCStr("\n\u65b0\u578b\u30b3\u30ed\u30ca\u30a6\u30a4\u30eb\u30b9\u306f"));}),_Xs=new T2(0,_Xq,_Xr),_Xt=new T2(1,_Xs,_Xp),_Xu=new T(function(){return B(unCStr("s2"));}),_Xv=new T(function(){return B(unCStr("\n\u300c\u306d\u3048\u306d\u3048 \u7a81\u7136\u3060\u3051\u3069 \u30cd\u30b3\u3063\u3066\u597d\u304d\uff1f{da}{e.b=0.m0:s2Q1}{e.b=1.m0:s2Q2}{e.b=2.m0:s2Q3}{e.b=3.m0:s2Q4}{e.b=4.m0:s2Q5}{e.vP.m1:s2P}{e.vI.m1:s2I}{e.vH.m1:s2H}{e.vN.m1:s2N}{e.bJ.m1:s2J0}{e.bB.m1:s2B0}{e.e/.m1:s2Not}{e.uR.r}{e.==.m1:s2c}{ch.\u597d\u304d,s2_1.\u304d\u3089\u3044,s2_2.\u3075\u3064\u3046,s2_3}"));}),_Xw=new T2(0,_Xu,_Xv),_Xx=new T2(1,_Xw,_Xt),_Xy=new T(function(){return B(unCStr("s1c"));}),_Xz=new T(function(){return B(unCStr("\n\u300c\u3042\u306a\u305f\u306f \u79c1\u3002\n\u300c\u79c1\u306f \u4e16\u754c\u3002\n\u3048\uff1f \u306a\u306b\uff1f \u3060\u308c\uff1f\u3002\n\u300c\u305d\u308c\u3067\u306f \u6b21\u306b\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046{p.0,3.n,Ex}{e.un.l}{e.c1.m1:s2}"));}),_XA=new T2(0,_Xy,_Xz),_XB=new T2(1,_XA,_Xx),_XC=new T(function(){return B(unCStr("s1J1"));}),_XD=new T(function(){return B(unCStr("\n\u300c\u307e\u305a\u306f \u30ea\u30c7\u30e5\u30fc\u30b9\uff01\u3002\n\u300c\u3053\u308c\u306f \u524a\uff1a\u3055\u304f\uff1a\u6e1b\uff1a\u3052\u3093\uff1a\u3059\u308b \u3068\u3044\u3075\u3053\u3068\u3060\u3002\n\u3062\u3083\u3042 \u306f\u3058\u3081\u304b\u3089 \u3055\u3046\u8a00\u3063\u3066\u3088\u306d\u3002\n\u300c\u4eba\u306e\u8a71\u3092\u906e\u308b\u3082\u306e\u3067\u306f\u306a\u3044\uff01\u3002\u6700\u5f8c\u307e\u3067\u3088\u3046\u3046\u3046\u3046\u304f \u805e\u304d\u306a\u3055\u3044\uff01\u3002\n\u3046\u308f\u3063 \u3081\u3093\u3069\u304f\u3055\u3044\u3084\u3064\u3060\u30fb\u30fb\u30fb\u3002\n\u300c\u3046\u3093\uff1f\n\u3044\u3084 \u306a\u3093\u3067\u3082\u30fb\u30fb\u30fb\n\u300c\u4eba\u985e\u306f \u7279\u306b\u5148\u9032\u56fd\u306b\u304a\u3044\u3066\u306f \u305d\u306e\u5bcc\u306b\u7518\u3093\u3058\u305f\u3053\u3068\u306b\u3088\u308a \u4eba\u3005\u306e\u6d88\u8cbb\u306b\u6b6f\u6b62\u3081\u304c\u52b9\u304b\u306a\u304f\u306a\u3063\u3066\u3044\u308b\u3002\n\u30fb\u30fb\u30fb\u3002\n\u300c\u30fb\u30fb\u30fb\u3002\n\u30fb\u30fb\u30fb\u3002\n\u300c\u304a\u3044\uff01\u3002\n\u3048\uff1f \u4f55\uff1f\u3002\n\u300c\u30ca\u30cb \u3067\u306f\u306a\u3044\uff01 \u3061\u3083\u3093\u3068\u8074\u3044\u3066\u308b\u306e\u304b\uff01\u3002\n\u3044\u3084 \u3042\u3093\u305f\u304c \u8a71\u3092\u906e\u308b\u306a \u3068\u304b\u8a00\u3063\u305f\u304b\u3089\u9ed9\u3063\u3066\u308b\u3060\u3051\u3067\u3057\u3087\u3002\n\u300c\u8074\u3044\u3066\u3090\u308b\u306a\u3089 \u76f8\u69cc\u304f\u3089\u3044\u6253\u3061\u306a\u3055\u3044\uff01\u3002\n\u306f\u3042\u30fb\u30fb\u30fb\u3002\n\u300c\u5927\u91cf\u6d88\u8cbb\u306b\u306f \u5927\u91cf\u306e\u30a8\u30cd\u30eb\u30ae\u30fc\u304c\u5fc5\u8981\u3060\u3002\n\u300c\u305d\u3082\u305d\u3082 \u30a8\u30cd\u30eb\u30ae\u30fc\u306f \u4f55\u3092\u6d88\u8cbb\u3059\u308b\u3053\u3068\u306b\u3088\u308a\u5f97\u3089\u308c\u3066\u3090\u308b\u304b\u77e5\u3063\u3066\u3090\u308b\u304b\uff1f\u3002\n\u3048\uff1f \u98df\u3079\u3082\u306e\uff1f\u3002\n\u300c\u98df\u7269\u306f\u7121\u8ad6\u3060\u304c \u6628\u4eca\u306e\u7d4c\u6e08\u6d3b\u52d5\u306b\u6b20\u304b\u305b\u306a\u3044\u30a8\u30cd\u30eb\u30ae\u30fc\u6e90\u304c\u3042\u308b\u3067\u3042\u3089\u3046\uff1f\u3002\n\u30fb\u30fb\u30fb\u3042\u306e\u30fc \u3082\u3046\u3061\u3087\u3063\u3068\u5206\u304b\u308a\u3084\u3059\u3044\u65e5\u672c\u8a9e\u3067\u3088\u308d\u3057\u304f\u3002\n\u300c\u5168\u304f\u6559\u990a\u306e\u306a\u3044\u4eba\u9593\u306f\u3053\u308c\u3060\u304b\u3089\u56f0\u308b\u3002\n\u300c\u305d\u3082\u305d\u3082\u793c\u5100\u304c\u306a\u3063\u3066\u304a\u3089\u3093\u3002\u305d\u308c\u304c\u4eba\u306b\u3082\u306e\u3092\u805e\u304f\u614b\u5ea6\u304b\uff1f\u3002\n\u3044\u3084 \u3079\u3064\u306b\u4f55\u3082\u5c0b\u306d\u3066\u306a\u3044\u3057\u3002\n\u300c\u304a\u524d\u304c\u7121\u77e5\u3067\u3042\u308b\u3053\u3068\u3092\u6190\u307f \u6559\u3048\u3066\u3084\u3089\u3046\u3068\u3044\u3075\u306e\u3060\u3089\u3046\u3002\n\u3042\u3093\u305f\u3053\u305d\u7121\u793c\u3060\u306a\u3002\n\u300c\u306a\u3093\u3060\u3068\uff01\u3002\n\u306f\u3042 \u307e\u3046\u3044\u3044\u3084 \u3055\u3044\u306a\u3089\u30fc\u3002"));}),_XE=new T2(0,_XC,_XD),_XF=new T2(1,_XE,_XB),_XG=new T(function(){return B(unCStr("s1J0"));}),_XH=new T(function(){return B(unCStr("\n\u300c\u79c1\u306f \u3042\u308b\u653f\u5e9c\u6a5f\u95a2\u6240\u5c5e\u306e \u30b5\u30a4\u30a8\u30f3\u30c6\u30a3\u30b9\u30c8\u3060\u3002\n\u300c\u73fe\u5728 \u5730\u7403\u74b0\u5883\u306f \u5371\u6a5f\u7684\u72b6\u614b\u306b\u7f6e\u304b\u308c\u3066\u3090\u308b\u3002\u6211\u3005\u4eba\u985e\u304c \u5354\u529b\u3057\u3066\u3053\u308c\u306b\u5c0d\u51e6\u3057\u306a\u3051\u308c\u3070 \u5c06\u4f86\u53d6\u308a\u8fd4\u3057\u306e\u3064\u304b\u306a\u3044\u4e8b\u614b\u3092\u62db\u304f\u3053\u3068\u306b\u306a\u308b\u3060\u3089\u3046\u3002\n\u306f\u3042\u30fb\u30fb\u30fb\u3002\n\u300c\u306f\u3042\u30fb\u30fb\u30fb\u3067\u306f\u306a\u3044\u305e\u3002\u771f\u5263\u306b\u8003\u3078\u3066\u307f\u306a\u3055\u3044\u3002\u3042\u306a\u305f\u306e\u884c\u52d5\u306e\u3072\u3068\u3064\u3072\u3068\u3064\u304c \u5730\u7403\u3092\u5b88\u308b\u304b \u6ec5\u307c\u3059\u304b \u6c7a\u3081\u308b\u3068\u8a00\u3063\u3066\u3082\u904e\u8a00\u3067\u306f\u306a\u3044\u306e\u3060\u3002\n\u30fb\u30fb\u30fb\u3063\u3066\u8a00\u306f\u308c\u3066\u3082 \u4f8b\u3078\u3070\u3069\u3093\u306a\u3053\u3068\u3092\u6c23\u3092\u3064\u3051\u308c\u3070\u3044\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c3R\u3060\u3088\u541b\u3002\u30ea\u30c7\u30e5\u30fc\u30b9\u3002\u30ea\u30e6\u30fc\u30ba\u3002\u30ea\u30b5\u30a4\u30af\u30eb\u3002\n\u3042\u30fc \u306a\u3093\u304b\u5b78\u6821\u3067\u304d\u3044\u305f\u3053\u3068\u3042\u308b\u306a\u3002\n\u300c\u805e\u3044\u305f\u3053\u3068\u304c\u3042\u308b\uff1f \u305d\u308c\u3067\u74b0\u5883\u304c\u5b88\u308c\u308b\u3068\u601d\u3075\u306e\u304b\u306d\uff1f \u5be6\u8e10\u3057\u306a\u3051\u308c\u3070\u610f\u5473\u306a\u3044\u306e\u3060\u3088\u3002\n\u30fb\u30fb\u30fb\u3067 \u4f55\u3059\u308c\u3070\u3044\u3044\u3093\u3067\u3057\u305f\u3063\u3051\uff1f\u3002\n\u300c\u306a\u3093\u3068\uff01\u3002 \u3044\u3084\u306f\u3084 \u541b\u306e\u3084\u3046\u306a\u8005\u304c\u5c11\u6578\u6d3e\u3067\u3042\u3063\u3066\u304f\u308c\u308c\u3070\u826f\u3044\u306e\u3060\u304c\u30fb\u30fb\u30fb\u3002\n\u300c\u3088\u308d\u3057\u3044\u3002\u3072\u3068\u3064\u3072\u3068\u3064\u8aac\u660e\u3059\u308b\u304b\u3089 \u3088\u304f\u805e\u304d\u306a\u3055\u3044\u3002\n\u30fb\u30fb\u30fb\u306a\u3093\u304b\u5049\u3055\u3046\u3060\u306a \u3053\u306e\u3072\u3068\u30fb\u30fb\u30fb\u3002\n\u300c\u4f55\u304b\u8a00\u3063\u305f\u304b\uff1f\u3002\n\u3044 \u3044\u3048 \u4f55\u3067\u3082\u306a\u3044\u3067\u3059\u30fb\u30fb\u30fb"));}),_XI=new T2(0,_XG,_XH),_XJ=new T2(1,_XI,_XF),_XK=new T(function(){return B(unCStr("s1S1"));}),_XL=new T(function(){return B(unCStr("\n\u300c\u6e29\u5ba4\u52b9\u679c\u30ac\u30b9\u3068\u3044\u3075\u8a00\u8449\u3092\u3054\u5b58\u77e5\u3067\u3059\u304b\uff1f\u3002\n\u3048\u3063\u3068 \u3042\u308c\u3060\u3088\u306d \u5730\u7403\u6e29\u6696\u5316\u306e\u539f\u56e0\u306b\u306a\u3063\u3066\u308b\u3063\u3066\u3044\u3075\u30fb\u30fb\u30fb\u30fb\u30fb\u4e8c\u9178\u5316\u70ad\u7d20\uff01\uff01\u3002\n\u300c\u78ba\u304b\u306b\u305d\u308c\u3082 \u3055\u3046\u306a\u306e\u3067\u3059\u304c \u305d\u308c\u3088\u308a\u3082\u3063\u3068 \u6e29\u5ba4\u52b9\u679c\u306e\u9ad8\u3044\u3082\u306e\u304c\u3042\u308a\u307e\u3059\u3002\n\u3048\uff1f\u30fb\u30fb\u30fb\u3046\u30fc\u3093 \u5929\u7136\u30ac\u30b9 \u3068\u304b\uff1f\u3002\n\u300c\u6c34\u84b8\u6c17\u3067\u3059\u3002\n\u6c34\u84b8\u6c23\u30fb\u30fb\u30fb\u6c34\uff01\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059 \u6c34\u3067\u3059\u3002 \u6c34\u306f\u5927\u6c23\u4e2d\u306b\u3042\u3063\u3066 \u6700\u3082\u6e29\u5ba4\u52b9\u679c\u306b\u8ca2\u732e\u3057\u3066\u3090\u307e\u3059\u3002\n\u8ca2\u732e\u30fb\u30fb\u30fb\u3063\u3066\u30fb\u30fb\u30fb\n\u300c\u8ca2\u732e\u3067\u3059\u3002 \u305d\u308c\u304c\u306a\u3051\u308c\u3070 \u5730\u7403\u306f\u4eba\u985e\u306e\u4f4f\u3081\u306a\u3044\u4e0d\u6bdb\u306e\u5730\u3067\u3059\u3002\n\u3067\u3082 \u3042\u308c\u3067\u3057\u3087\uff1f \u6700\u8fd1\u4e8c\u9178\u5316\u70ad\u7d20\u304c\u5897\u3048\u3066 \u6e29\u6696\u5316\u306b\u306a\u3063\u3066\u3090\u308b\u3093\u3067\u3059\u3088\u306d\uff1f\u3002\n\u300c\u306a\u305c \u3055\u3046\u8a00\u3078\u308b\u306e\u3067\u3059\u304b\uff1f\u3002\n\u306a\u305c\u3063\u3066\u30fb\u30fb\u30fb\u79d1\u5b78\u8005\u304c\u3055\u3046\u8a00\u3063\u3066\u308b\u3067\u3057\u3087\uff1f\u3002\n\u300c\u79d1\u5b78\u8005\u304c\u3055\u3046\u8a00\u3063\u3066\u3090\u308b\u304b\u3089 \u3068\u3044\u3075\u7406\u7531\u3067 \u7269\u4e8b\u3092\u8003\u3078\u308b\u306e\u306f \u975e\u79d1\u5b78\u7684\u3067\u3059\u306d\u3002\n\u4e8c\u9178\u5316\u70ad\u7d20\u304c\u6e29\u5ba4\u52b9\u679c\u30ac\u30b9\u3067 \u305d\u308c\u304c\u5897\u3048\u305f\u304b\u3089 \u6e29\u6696\u5316\u304c\u8d77\u3053\u3063\u3066\u3090\u308b\u3093\u3067\u306f\u306a\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c\u5927\u6c23\u4e2d\u306e\u4e8c\u9178\u5316\u70ad\u7d20\u306e\u5272\u5408\u306f \u304a\u3088\u305d400ppm \u3067\u3059\u3002\n\u3048\uff1f\n\u300c0.04\u30d1\u30fc\u30bb\u30f3\u30c8\u3068\u8a00\u3063\u305f\u3089\u5206\u304b\u308a\u3084\u3059\u3044\u3067\u305b\u3046\u304b\uff1f\u3002 \u5c0d\u3057\u3066\u6c34\u84b8\u6c23\u306e\u5272\u5408\u306f \u6e7f\u5ea6\u306b\u3088\u308a\u307e\u3059\u304c \u3060\u3044\u305f\u30445\u30d1\u30fc\u30bb\u30f3\u30c8\u7a0b\u5ea6\u3067\u3059\u3002\n\u6c34\u306e\u65b9\u304c \u5168\u7136\u591a\u3044\u306a\u30fb\u30fb\u30fb\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u4eee\u306b\u4e8c\u9178\u5316\u70ad\u7d20\u306e\u5272\u5408\u304c \u4eca\u306e\u5341\u500d\u306b\u306a\u3063\u305f\u3068\u3057\u3066 \u305d\u306e\u5927\u6c23\u4e2d\u306e\u5272\u5408\u306f 0.4\u30d1\u30fc\u30bb\u30f3\u30c8\u3067\u3059\u3002 \u6c34\u84b8\u6c23\u306b\u306f\u53ca\u3073\u307e\u305b\u3093\u3002\n\u300c\u305d\u3057\u3066 \u6c34\u84b8\u6c23\u306e\u65b9\u304c \u6e29\u5ba4\u52b9\u679c\u304c\u9ad8\u3044\u306e\u3067\u3059\u3002 \u79c1\u306e\u8a00\u306f\u3046\u3068\u3057\u3066\u3090\u308b\u3053\u3068\u304c\u5206\u304b\u308a\u307e\u3059\u304b\uff1f\u3002\n\u30fb\u30fb\u30fb\u4e8c\u9178\u5316\u70ad\u7d20\u304c\u6e29\u6696\u5316\u306e\u539f\u56e0\u30fb\u30fb\u30fb\u3067\u306f\u306a\u3044\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u79d1\u5b78\u7684\u306a\u30c7\u30fc\u30bf\u304b\u3089 \u5408\u7406\u7684\u306b\u8003\u3078\u308c\u3070 \u4e8c\u9178\u5316\u70ad\u7d20\u304c\u5897\u3048\u3066\u3082 \u5730\u7403\u306e\u6c17\u6e29\u306b\u307b\u3068\u3093\u3069\u5f71\u97ff\u3092\u8207\u3078\u306a\u3044\u3067\u3042\u308d\u3046\u3053\u3068\u304f\u3089\u3044 \u5c0f\u5b78\u751f\u3067\u3082\u5206\u304b\u308a\u307e\u3059\u3002 \u3067\u3059\u304c \u6b98\u5ff5\u306a\u304c\u3089 \u305d\u306e\u5c0f\u5b78\u751f\u9054\u304c\u901a\u3075\u5b78\u6821\u306b\u304a\u3044\u3066 \u975e\u79d1\u5b78\u7684\u306a\u8ff7\u4fe1\u304c\u5e38\u306b\u6559\u3078\u3089\u308c\u3066\u3090\u308b\u306e\u3067\u3059\u3002\n\u3069\u3046\u3057\u3066\u30fb\u30fb\u30fb\uff1f\u3002\n\u300c\u3055\u3066 \u3069\u3046\u3057\u3066\u3067\u305b\u3046\uff1f\u3002"));}),_XM=new T2(0,_XK,_XL),_XN=new T2(1,_XM,_XJ),_XO=new T(function(){return B(unCStr("s1S0"));}),_XP=new T(function(){return B(unCStr("\n\u300c\u79c1\u306f \u79d1\u5b78\u8005\u306e\u7aef\u304f\u308c\u3068\u3057\u3066 \u73fe\u5728\u306e\u74b0\u5883\u554f\u984c\u306e\u6349\u3078\u65b9\u306b\u5c0d\u3057 \u5927\u3044\u306b \u5371\u60e7\u3057\u3066\u3090\u307e\u3059\u3002\n\uff1f\uff1f\uff1f \u3042\u306e\u301c \u307e\u3046\u5c11\u3057\u5206\u304b\u308a\u3084\u3059\u304f \u8a71\u3057\u3066\u3082\u3089\u3078\u307e\u3059\uff1f\u3002\n\u300c\u3042\u3042 \u3059\u307f\u307e\u305b\u3093\u30fb\u30fb\u30fb\u3002 \u79c1\u306f \u305f\u3060 \u3044\u306f\u3086\u308b \u74b0\u5883\u554f\u984c\u3068\u3044\u3075\u3082\u306e\u304c \u554f\u984c\u3067\u3042\u308b \u3068\u8a34\u3078\u305f\u3044\u3060\u3051\u306a\u306e\u3067\u3059\u3002\n\u74b0\u5883\u554f\u984c\u304c\u30fb\u30fb\u30fb\u554f\u984c\uff1f \u3067\u3059\u304b\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u3048\u301c\u3068\u3067\u3059\u306d\u3002 \u8981\u306f \u5730\u7403\u74b0\u5883\u306b\u554f\u984c\u304c\u3042\u308b\u306e\u3067\u306f\u306a\u304f \u73fe\u5728\u306e\u5730\u7403\u74b0\u5883\u306e\u6271\u3072\u65b9 \u3068\u3089\u3078\u65b9\u306b\u554f\u984c\u304c\u3042\u308b \u3068\u8a00\u3063\u3066\u3090\u308b\u306e\u3067\u3059\u3002\n\u306f\u3042\u30fb\u30fb\u30fb\u3002\n\u300c\u4f8b\u3078\u3070 \u5730\u7403\u6e29\u6696\u5316\u554f\u984c \u3068\u3044\u3075\u3082\u306e\u304c\u3042\u308a\u307e\u3059\u3002\n\u3042\u3042 \u5730\u7403\u6e29\u6696\u5316\u306d\uff01 \u305d\u308c\u306a\u3089 \u77e5\u3063\u3066\u307e\u3059\u3088\u3002 \u30c6\u30ec\u30d3\u3067\u3082 \u3088\u304f\u3084\u3063\u3066\u3090\u307e\u3059\u3088\u306d\u3002\n\u300c\u306f\u3044\u3002 \u79c1\u9054\u306e\u898b\u5730\u304b\u3089 \u305d\u308c\u306b\u3064\u3044\u3066\u306e\u756a\u7d44\u306a\u3069\u3092\u898b\u308b\u3068 \u79d1\u5b78\u7684\u306b\u898b\u3066 \u305d\u308c\u3089\u306f \u4e0d\u6b63\u78ba\u306a\u60c5\u5831\u3067\u3059\u3002\n\u30fb\u30fb\u30fb\u3048\u3063\u3068\u30fb\u30fb\u30fb\u3069\u3046\u3044\u3075\u3053\u3068\u304b\u306a\uff1f\u3002\n\u300c\u30c6\u30ec\u30d3\u3067\u8a00\u3063\u3066\u3090\u308b\u3053\u3068\u306f \u9593\u9055\u3063\u3066\u3090\u308b \u3068\u8a00\u3072\u305f\u3044\u306e\u3067\u3059\u3002\n\u3048\uff1f \u3044\u3084 \u3067\u3082 \u5b78\u6821\u3067\u3082\u7fd2\u3075\u3060\u3089\u3046\u3057 \u4f55\u3088\u308a\u3082 \u653f\u5e9c\u304c \u74b0\u5883\u554f\u984c\u306b\u53d6\u308a\u7d44\u3093\u3067\u3090\u308b\u3093\u3062\u3083\u306a\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u305d\u3053\u304c\u3084\u3063\u304b\u3044\u306a\u3068\u3053\u308d\u306a\u306e\u3067\u3059\u3002 \u9593\u9055\u3063\u305f\u4e8b\u3092 \u5b78\u6821\u3067\u6559\u3078 \u570b\u3084\u81ea\u6cbb\u9ad4\u304c\u653f\u7b56\u3068\u3057\u3066\u5be6\u884c\u3057\u3066\u3090\u308b\u30fb\u30fb\u30fb\u3002\n\u3044\u3084\u3044\u3084 \u305d\u308c\u306f\u306a\u3044\u3067\u305b\u3046\u3002 \u3060\u3063\u3066 \u79d1\u5b78\u8005\u306e\u4eba\u305f\u3061\u304c\u96c6\u307e\u3063\u3066\u6c7a\u3081\u305f\u3084\u3046\u306a\u3053\u3068\u3092 \u6559\u3078\u305f\u308a \u653f\u6cbb\u5bb6\u304c\u3084\u3063\u305f\u308a\u3059\u308b\u3093\u3062\u3083\u306a\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c\u3082\u3061\u308d\u3093 \u3055\u3046\u3042\u3063\u3066\u6b32\u3057\u3044\u3093\u3067\u3059\u304c \u79c1\u3069\u3082\u304b\u3089\u898b\u3066 \u3055\u3046\u3044\u3063\u305f \u3044\u306f\u3086\u308b \uff1c\u79d1\u5b78\u8005\uff1e\u306f \u79d1\u5b78\u3092\u3084\u3063\u3066\u3090\u307e\u305b\u3093\u3002\n\uff1f\uff1f\uff1f \u3069\u3046\u3044\u3075\u3053\u3068\u304b\u306a\uff1f{e.bS.m1:s1S1}"));}),_XQ=new T2(0,_XO,_XP),_XR=new T2(1,_XQ,_XN),_XS=new T(function(){return B(unCStr("s1C0"));}),_XT=new T(function(){return B(unCStr("\n\u3042\u308c \u3053\u308c\u306f\u30cd\u30b3\uff1f \u3062\u3083\u306a\u3044\u306e\u304b\uff1f\u3002\n\u300c\u50d5\u306f\u3053\u3053\u3060\u3088\u3002\n\u3093\uff1f\n\u300c\u3061\u3087\u3063\u3068\u6b21\u5143\u304c\u9055\u3075\u6240\u30fb\u30fb\u30fb\u3002\u307e\u3042 \u305d\u308c\u306f\u3044\u3044\u3068\u3057\u3066\u3002\n\u300c\u305d\u308c\u306f \u6587\u5b57 C \u3060\u306d\u3002\n\u300c\u305d\u308c\u3092\u52d5\u304b\u3057\u3066 \u3069\u3053\u304b\u3078\u7f6e\u304b\u306a\u304d\u3083\u3044\u3051\u306a\u3044\u304b\u3082\u77e5\u308c\u306a\u3044\u3057 \u7f6e\u304b\u306a\u304f\u3066\u3044\u3044\u304b\u3082\u3057\u308c\u306a\u3044\u3002\n\uff1f\uff1f\uff1f\u306a\u3093\u3060\u305d\u308c\u3002\n\u300c\u3053\u3053\u306b\u306f \u554f\u984c\u304c3\u3064\u3042\u308b\u307f\u305f\u3044\u306a\u3093\u3060\u3002\u305d\u306e\u7b54\u3078\u306b\u306a\u308b\u3082\u306e\u3092 \u30a4\u30b3\u30fc\u30eb\u306e\u53f3\u306b\u7f6e\u304f\u3093\u3060\u3089\u3046\u306d\u3002\n\u300c\u898b\u305f\u3068\u3053\u308d \u6578\u5b57\u3084\u5c0f\u6578\u9ede\uff1f\u306f\u6301\u3066\u308b\u3051\u3069 C \u3068 O \u3068 H \u3068 X \u306f\u6301\u3066\u306a\u304f\u3066 \u52d5\u304b\u3059\u307f\u305f\u3044\u3060\u306d\u3002\n\u30fb\u30fb\u30fb\u30fb\u3002\n\u300c\u3042\u3068 \u3053\u3053\u306b\u306f \u4e8c\u4eba\u306e \u81ea\u79f0 \u79d1\u5b78\u8005\u304c\u3090\u308b\u3088\u3002\u5f7c\u3089\u3068\u8a71\u305b\u3070 \u554f\u984c\u3092\u89e3\u304f\u30d2\u30f3\u30c8\u304c\u5f97\u3089\u308c\u3055\u3046\u3060\u306d\u3002\n\u3066\u304b \u306a\u3093\u3067\u3053\u3093\u306a\u3053\u3068\u3057\u306a\u304d\u3083\u30fb\u30fb\u30fb\u3002\n\u300c\u3062\u3083 \u304c\u3093\u3070\u3063\u3066\u306d\u301c\u3002\u3042 \u3055\u3046\u3060\u3002\u8a00\u3072\u5fd8\u308c\u3066\u305f\u3002\n\u30fb\u30fb\u30fb\u306a\u3093\u3060\u3088\u3002\n\u300c\u3082\u3057\u884c\u304d\u8a70\u307e\u3063\u305f\u3089 \u53f3\u4e0b\u306b\u3042\u308b R \u3078\u98db\u3073\u3053\u3080\u3068\u3044\u3044\u3088\u3002\u305d\u308c\u3062\u3083\uff01\u3002\n\u98db\u3073\u3053\u3080\uff1f\uff1f\uff1f\u3002\u306a\u3093\u304b \u8272\u3005\u8aac\u660e\u4e0d\u8db3\u3060\u308d\u30fb\u30fb\u30fb"));}),_XU=new T2(0,_XS,_XT),_XV=new T2(1,_XU,_XR),_XW=new T2(1,_VZ,_XV),_XX=new T(function(){return B(unCStr("s1Q2"));}),_XY=new T(function(){return B(unCStr("\n\u5730\u7403\u306e\u6c17\u6e29\u306f\u6642\u4ee3\u306b\u3088\u3063\u3066\u5927\u304d\u304f\u8b8a\u5316\u3057\u3066\u304d\u305f\uff1f"));}),_XZ=new T2(0,_XX,_XY),_Y0=new T2(1,_XZ,_XW),_Y1=new T2(1,_VW,_Y0),_Y2=new T2(1,_VT,_Y1),_Y3=new T2(1,_VQ,_Y2),_Y4=new T2(1,_VN,_Y3),_Y5=new T2(1,_VK,_Y4),_Y6=new T2(1,_VH,_Y5),_Y7=new T2(1,_VE,_Y6),_Y8=new T2(1,_VB,_Y7),_Y9=new T(function(){return B(unCStr("initMsg"));}),_Ya=new T(function(){var _Yb=B(_Vs(_Y9,_Vy,_Y8));return new T2(0,_Yb.a,_Yb.b);}),_Yc=new T(function(){return E(E(_Ya).b);}),_Yd=new T(function(){return E(E(_Ya).a);}),_Ye=function(_Yf){if(!B(_4B(_fq,_Yf,_Yd))){return __Z;}else{return new F(function(){return _77(_Yc,B(_iC(_fq,_Yf,_Yd)));});}},_Yg=10,_Yh=15,_Yi=new T2(0,_Yh,_Yg),_Yj=new T2(1,_Yi,_10),_Yk=8,_Yl=7,_Ym=new T2(0,_Yl,_Yk),_Yn=new T2(1,_Ym,_Yj),_Yo=5,_Yp=new T2(0,_Yo,_Yo),_Yq=new T2(1,_Yp,_Yn),_Yr=4,_Ys=new T2(0,_Yr,_Yo),_Yt=new T2(1,_Ys,_10),_Yu=3,_Yv=new T2(0,_Yu,_Yu),_Yw=new T2(1,_Yv,_Yt),_Yx=2,_Yy=1,_Yz=new T2(0,_Yx,_Yy),_YA=new T2(1,_Yz,_Yw),_YB=new T(function(){return B(_a2("Check.hs:(81,7)-(86,39)|function chAnd"));}),_YC=38,_YD=new T(function(){return B(unCStr("@@@"));}),_YE=new T2(0,_Yx,_Yu),_YF=1,_YG=67,_YH=new T2(0,_YG,_YF),_YI=new T2(0,_YE,_YH),_YJ=new T2(0,_Yr,_Yr),_YK=57,_YL=new T2(0,_YK,_YF),_YM=new T2(0,_YJ,_YL),_YN=new T2(1,_YM,_10),_YO=0,_YP=new T2(0,_YO,_Yr),_YQ=51,_YR=new T2(0,_YQ,_YF),_YS=new T2(0,_YP,_YR),_YT=new T2(1,_YS,_YN),_YU=new T2(0,_Yr,_Yu),_YV=56,_YW=new T2(0,_YV,_YF),_YX=new T2(0,_YU,_YW),_YY=new T2(1,_YX,_YT),_YZ=new T2(1,_YI,_YY),_Z0=new T2(0,_YO,_Yu),_Z1=50,_Z2=new T2(0,_Z1,_YF),_Z3=new T2(0,_Z0,_Z2),_Z4=new T2(1,_Z3,_YZ),_Z5=new T2(0,_Yr,_Yx),_Z6=55,_Z7=new T2(0,_Z6,_YF),_Z8=new T2(0,_Z5,_Z7),_Z9=new T2(1,_Z8,_Z4),_Za=new T2(0,_YO,_Yx),_Zb=49,_Zc=new T2(0,_Zb,_YF),_Zd=new T2(0,_Za,_Zc),_Ze=new T2(1,_Zd,_Z9),_Zf=new T2(0,_Yu,_YO),_Zg=43,_Zh=new T2(0,_Zg,_YF),_Zi=new T2(0,_Zf,_Zh),_Zj=new T2(1,_Zi,_Ze),_Zk=new T2(0,_Yy,_YO),_Zl=61,_Zm=new T2(0,_Zl,_YF),_Zn=new T2(0,_Zk,_Zm),_Zo=new T2(1,_Zn,_Zj),_Zp=new T2(0,_YO,_YO),_Zq=53,_Zr=new T2(0,_Zq,_YF),_Zs=new T2(0,_Zp,_Zr),_Zt=new T2(1,_Zs,_Zo),_Zu=6,_Zv=new T2(0,_Zu,_Yl),_Zw=2,_Zx=82,_Zy=new T2(0,_Zx,_Zw),_Zz=new T2(0,_Zv,_Zy),_ZA=new T2(1,_Zz,_10),_ZB=48,_ZC=new T2(0,_ZB,_AQ),_ZD=new T2(0,_Yr,_Yl),_ZE=new T2(0,_ZD,_ZC),_ZF=new T2(1,_ZE,_ZA),_ZG=new T2(0,_Yx,_Yl),_ZH=new T2(0,_ZG,_ZC),_ZI=new T2(1,_ZH,_ZF),_ZJ=52,_ZK=new T2(0,_ZJ,_AQ),_ZL=new T2(0,_YO,_Yl),_ZM=new T2(0,_ZL,_ZK),_ZN=new T2(1,_ZM,_ZI),_ZO=3,_ZP=79,_ZQ=new T2(0,_ZP,_ZO),_ZR=new T2(0,_Yo,_Zu),_ZS=new T2(0,_ZR,_ZQ),_ZT=new T2(1,_ZS,_ZN),_ZU=46,_ZV=new T2(0,_ZU,_AQ),_ZW=new T2(0,_Yu,_Zu),_ZX=new T2(0,_ZW,_ZV),_ZY=new T2(1,_ZX,_ZT),_ZZ=new T2(0,_Yy,_Zu),_100=new T2(0,_ZZ,_ZQ),_101=new T2(1,_100,_ZY),_102=new T2(0,_Z1,_AQ),_103=new T2(0,_Zu,_Yo),_104=new T2(0,_103,_102),_105=new T2(1,_104,_101),_106=new T2(0,_Yu,_Yo),_107=72,_108=new T2(0,_107,_ZO),_109=new T2(0,_106,_108),_10a=new T2(1,_109,_105),_10b=new T2(0,_YO,_Yo),_10c=new T2(0,_10b,_102),_10d=new T2(1,_10c,_10a),_10e=74,_10f=new T2(0,_10e,_YF),_10g=new T2(0,_Yo,_Yr),_10h=new T2(0,_10g,_10f),_10i=new T2(1,_10h,_10d),_10j=new T2(0,_Yu,_Yr),_10k=88,_10l=new T2(0,_10k,_ZO),_10m=new T2(0,_10j,_10l),_10n=new T2(1,_10m,_10i),_10o=new T2(0,_Yy,_Yr),_10p=83,_10q=new T2(0,_10p,_YF),_10r=new T2(0,_10o,_10q),_10s=new T2(1,_10r,_10n),_10t=new T2(0,_Yo,_Yu),_10u=new T2(0,_YG,_ZO),_10v=new T2(0,_10t,_10u),_10w=new T2(1,_10v,_10s),_10x=54,_10y=new T2(0,_10x,_AQ),_10z=new T2(0,_Z0,_10y),_10A=new T2(1,_10z,_10w),_10B=new T2(0,_Yx,_Yx),_10C=new T2(0,_10B,_Zm),_10D=new T2(1,_10C,_10A),_10E=new T2(0,_Yy,_Yx),_10F=new T2(0,_10E,_YR),_10G=new T2(1,_10F,_10D),_10H=81,_10I=new T2(0,_10H,_YF),_10J=new T2(0,_Za,_10I),_10K=new T2(1,_10J,_10G),_10L=new T2(0,_Yz,_Zm),_10M=new T2(1,_10L,_10K),_10N=new T2(0,_Yy,_Yy),_10O=new T2(0,_10N,_Z2),_10P=new T2(1,_10O,_10M),_10Q=new T2(0,_YO,_Yy),_10R=new T2(0,_10Q,_10I),_10S=new T2(1,_10R,_10P),_10T=new T2(0,_Yx,_YO),_10U=new T2(0,_10T,_Zm),_10V=new T2(1,_10U,_10S),_10W=new T2(0,_Zk,_Zc),_10X=new T2(1,_10W,_10V),_10Y=new T2(0,_Zp,_10I),_10Z=new T2(1,_10Y,_10X),_110=new T2(0,_Zp,_YH),_111=new T2(0,_ZP,_YF),_112=new T2(0,_Zk,_111),_113=86,_114=new T2(0,_113,_YF),_115=new T2(0,_10T,_114),_116=73,_117=new T2(0,_116,_YF),_118=new T2(0,_Zf,_117),_119=68,_11a=new T2(0,_119,_YF),_11b=new T2(0,_Yr,_YO),_11c=new T2(0,_11b,_11a),_11d=new T2(0,_Yo,_YO),_11e=new T2(0,_11d,_Zc),_11f=new T2(0,_Zu,_YO),_11g=new T2(0,_11f,_YL),_11h=new T2(0,_Yl,_Yy),_11i=new T2(0,_11h,_117),_11j=new T2(0,_Yk,_Yy),_11k=84,_11l=new T2(0,_11k,_YF),_11m=new T2(0,_11j,_11l),_11n=9,_11o=new T2(0,_11n,_Yy),_11p=new T2(0,_11o,_117),_11q=new T2(0,_Yg,_Yy),_11r=new T2(0,_11q,_114),_11s=69,_11t=new T2(0,_11s,_YF),_11u=11,_11v=new T2(0,_11u,_Yy),_11w=new T2(0,_11v,_11t),_11x=12,_11y=new T2(0,_11x,_Yy),_11z=new T2(0,_11y,_Zm),_11A=77,_11B=new T2(0,_11A,_YF),_11C=new T2(0,_Za,_11B),_11D=65,_11E=new T2(0,_11D,_YF),_11F=new T2(0,_10E,_11E),_11G=new T2(0,_10B,_10q),_11H=75,_11I=new T2(0,_11H,_YF),_11J=new T2(0,_Yu,_Yx),_11K=new T2(0,_11J,_11I),_11L=new T2(0,_Z5,_Zm),_11M=new T2(0,_Z0,_114),_11N=new T2(0,_Yy,_Yu),_11O=new T2(0,_11N,_11E),_11P=new T2(0,_Yv,_YH),_11Q=new T2(0,_YU,_117),_11R=78,_11S=new T2(0,_11R,_YF),_11T=new T2(0,_10t,_11S),_11U=new T2(0,_Zu,_Yu),_11V=new T2(0,_11U,_11t),_11W=new T2(0,_Yl,_Yu),_11X=new T2(0,_11W,_Zm),_11Y=80,_11Z=new T2(0,_11Y,_ZO),_120=new T2(0,_11x,_Yu),_121=new T2(0,_120,_11Z),_122=new T2(0,_YP,_YH),_123=new T2(0,_10o,_111),_124=new T2(0,_Yx,_Yr),_125=new T2(0,_124,_11S),_126=new T2(0,_10j,_11l),_127=new T2(0,_YJ,_11E),_128=47,_129=new T2(0,_128,_AQ),_12a=new T2(0,_11x,_11n),_12b=new T2(0,_12a,_129),_12c=new T2(1,_12b,_10),_12d=new T2(0,_Yk,_11n),_12e=new T2(0,_12d,_129),_12f=new T2(1,_12e,_12c),_12g=new T2(0,_Yy,_11n),_12h=new T2(0,_12g,_Zy),_12i=new T2(1,_12h,_12f),_12j=new T2(0,_116,_ZO),_12k=new T2(0,_11x,_Yl),_12l=new T2(0,_12k,_12j),_12m=new T2(1,_12l,_12i),_12n=new T2(0,_Yk,_Yl),_12o=new T2(0,_12n,_108),_12p=new T2(1,_12o,_12m),_12q=new T2(0,_ZD,_10f),_12r=new T2(1,_12q,_12p),_12s=new T2(0,_11R,_ZO),_12t=new T2(0,_Yy,_Yl),_12u=new T2(0,_12t,_12s),_12v=new T2(1,_12u,_12r),_12w=new T2(0,_11x,_Yo),_12x=new T2(0,_12w,_108),_12y=new T2(1,_12x,_12v),_12z=66,_12A=new T2(0,_12z,_YF),_12B=new T2(0,_Yk,_Yo),_12C=new T2(0,_12B,_12A),_12D=new T2(1,_12C,_12y),_12E=new T2(0,_Yl,_Yr),_12F=new T2(0,_12E,_Zm),_12G=new T2(1,_12F,_12D),_12H=new T2(0,_Zu,_Yr),_12I=new T2(0,_12H,_11l),_12J=new T2(1,_12I,_12G),_12K=new T2(0,_10g,_YH),_12L=new T2(1,_12K,_12J),_12M=new T2(1,_127,_12L),_12N=new T2(1,_126,_12M),_12O=new T2(1,_125,_12N),_12P=new T2(1,_123,_12O),_12Q=new T2(1,_122,_12P),_12R=new T2(1,_121,_12Q),_12S=new T2(1,_11X,_12R),_12T=new T2(1,_11V,_12S),_12U=new T2(1,_11T,_12T),_12V=new T2(1,_11Q,_12U),_12W=new T2(1,_11P,_12V),_12X=new T2(1,_YI,_12W),_12Y=new T2(1,_11O,_12X),_12Z=new T2(1,_11M,_12Y),_130=new T2(1,_11L,_12Z),_131=new T2(1,_11K,_130),_132=new T2(1,_11G,_131),_133=new T2(1,_11F,_132),_134=new T2(1,_11C,_133),_135=new T2(1,_11z,_134),_136=new T2(1,_11w,_135),_137=new T2(1,_11r,_136),_138=new T2(1,_11p,_137),_139=new T2(1,_11m,_138),_13a=new T2(1,_11i,_139),_13b=new T2(0,_Zu,_Yy),_13c=new T2(0,_13b,_10q),_13d=new T2(1,_13c,_13a),_13e=new T2(0,_Yo,_Yy),_13f=new T2(0,_13e,_111),_13g=new T2(1,_13f,_13d),_13h=new T2(0,_11Y,_YF),_13i=new T2(0,_Yr,_Yy),_13j=new T2(0,_13i,_13h),_13k=new T2(1,_13j,_13g),_13l=new T2(0,_Zx,_YF),_13m=new T2(0,_Yz,_13l),_13n=new T2(1,_13m,_13k),_13o=new T2(0,_10N,_YH),_13p=new T2(1,_13o,_13n),_13q=new T2(0,_10Q,_13h),_13r=new T2(1,_13q,_13p),_13s=new T2(0,_Yl,_YO),_13t=new T2(0,_13s,_Zm),_13u=new T2(1,_13t,_13r),_13v=new T2(1,_11g,_13u),_13w=new T2(1,_11e,_13v),_13x=new T2(1,_11c,_13w),_13y=new T2(1,_118,_13x),_13z=new T2(1,_115,_13y),_13A=new T2(1,_112,_13z),_13B=new T2(1,_110,_13A),_13C=new T2(1,_13B,_10),_13D=new T2(1,_10Z,_13C),_13E=new T2(1,_Zt,_13D),_13F=6,_13G=7,_13H=8,_13I=4,_13J=5,_13K=function(_13L){var _13M=E(_13L);if(!_13M._){return __Z;}else{var _13N=_13M.b,_13O=E(_13M.a),_13P=_13O.b,_13Q=E(_13O.a),_13R=function(_13S){if(E(_13Q)==32){return new T2(1,_13O,new T(function(){return B(_13K(_13N));}));}else{switch(E(_13P)){case 0:return new T2(1,new T2(0,_13Q,_AQ),new T(function(){return B(_13K(_13N));}));case 1:return new T2(1,new T2(0,_13Q,_13G),new T(function(){return B(_13K(_13N));}));case 2:return new T2(1,new T2(0,_13Q,_Zw),new T(function(){return B(_13K(_13N));}));case 3:return new T2(1,new T2(0,_13Q,_ZO),new T(function(){return B(_13K(_13N));}));case 4:return new T2(1,new T2(0,_13Q,_13I),new T(function(){return B(_13K(_13N));}));case 5:return new T2(1,new T2(0,_13Q,_13J),new T(function(){return B(_13K(_13N));}));case 6:return new T2(1,new T2(0,_13Q,_13F),new T(function(){return B(_13K(_13N));}));case 7:return new T2(1,new T2(0,_13Q,_13G),new T(function(){return B(_13K(_13N));}));default:return new T2(1,new T2(0,_13Q,_13H),new T(function(){return B(_13K(_13N));}));}}};if(E(_13Q)==32){return new F(function(){return _13R(_);});}else{switch(E(_13P)){case 0:return new T2(1,new T2(0,_13Q,_13H),new T(function(){return B(_13K(_13N));}));case 1:return new F(function(){return _13R(_);});break;case 2:return new F(function(){return _13R(_);});break;case 3:return new F(function(){return _13R(_);});break;case 4:return new F(function(){return _13R(_);});break;case 5:return new F(function(){return _13R(_);});break;case 6:return new F(function(){return _13R(_);});break;case 7:return new F(function(){return _13R(_);});break;default:return new F(function(){return _13R(_);});}}}},_13T=function(_13U){var _13V=E(_13U);return (_13V._==0)?__Z:new T2(1,new T(function(){return B(_13K(_13V.a));}),new T(function(){return B(_13T(_13V.b));}));},_13W=function(_13X){var _13Y=E(_13X);if(!_13Y._){return __Z;}else{var _13Z=_13Y.b,_140=E(_13Y.a),_141=_140.b,_142=E(_140.a),_143=function(_144){if(E(_142)==32){return new T2(1,_140,new T(function(){return B(_13W(_13Z));}));}else{switch(E(_141)){case 0:return new T2(1,new T2(0,_142,_AQ),new T(function(){return B(_13W(_13Z));}));case 1:return new T2(1,new T2(0,_142,_YF),new T(function(){return B(_13W(_13Z));}));case 2:return new T2(1,new T2(0,_142,_Zw),new T(function(){return B(_13W(_13Z));}));case 3:return new T2(1,new T2(0,_142,_ZO),new T(function(){return B(_13W(_13Z));}));case 4:return new T2(1,new T2(0,_142,_13I),new T(function(){return B(_13W(_13Z));}));case 5:return new T2(1,new T2(0,_142,_13J),new T(function(){return B(_13W(_13Z));}));case 6:return new T2(1,new T2(0,_142,_13F),new T(function(){return B(_13W(_13Z));}));case 7:return new T2(1,new T2(0,_142,_YF),new T(function(){return B(_13W(_13Z));}));default:return new T2(1,new T2(0,_142,_13H),new T(function(){return B(_13W(_13Z));}));}}};if(E(_142)==32){return new F(function(){return _143(_);});}else{if(E(_141)==8){return new T2(1,new T2(0,_142,_AQ),new T(function(){return B(_13W(_13Z));}));}else{return new F(function(){return _143(_);});}}}},_145=function(_146){var _147=E(_146);return (_147._==0)?__Z:new T2(1,new T(function(){return B(_13W(_147.a));}),new T(function(){return B(_145(_147.b));}));},_148=new T(function(){return B(unCStr("msgW"));}),_149=new T(function(){return B(_Ye(_148));}),_14a=new T(function(){return B(_kt("Check.hs:132:22-33|(ch : po)"));}),_14b=new T(function(){return B(_a2("Check.hs:(102,1)-(146,21)|function trEvent"));}),_14c=new T(function(){var _14d=E(_YD);if(!_14d._){return E(_dJ);}else{return E(_14d.a);}}),_14e=new T(function(){return B(_UZ(_Yo,5,_Zt));}),_14f=function(_14g){var _14h=E(_14g);return E(_TA);},_14i=new T(function(){return B(unCStr("msgR"));}),_14j=new T(function(){return B(_Ye(_14i));}),_14k=function(_14l,_14m,_14n,_14o,_14p,_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q){var _14R=E(_14m);if(!_14R._){return E(_14b);}else{var _14S=_14R.b,_14T=E(_14R.a);switch(E(_14T)){case 97:var _14U=new T(function(){var _14V=E(_14S);if(!_14V._){return E(_14a);}else{return new T2(0,_14V.a,_14V.b);}}),_14W=new T(function(){var _14X=B(_Q5(E(_14U).b));return new T2(0,_14X.a,_14X.b);}),_14Y=B(_za(B(_mJ(_Ty,new T(function(){return E(E(_14W).b);})))));if(!_14Y._){return E(_TF);}else{if(!E(_14Y.b)._){var _14Z=new T(function(){var _150=B(_za(B(_mJ(_Ty,new T(function(){return E(E(_14W).a);})))));if(!_150._){return E(_TF);}else{if(!E(_150.b)._){return E(_150.a);}else{return E(_TE);}}},1),_151=B(_m9(_14Z,E(_14Y.a),new T(function(){return E(E(_14U).a);}),_AQ,_14o));return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(_14y),e:E(_14z),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};}else{return E(_TE);}}break;case 104:var _152=B(_13T(_14o));return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(_14y),e:E(_14z),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};case 106:var _153=B(_za(B(_mJ(_Ty,_14S))));return (_153._==0)?E(_TF):(E(_153.b)._==0)?{_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(_14y),e:E(_14z),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:E(_153.a),l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q}:E(_TE);case 108:return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(B(_Tn(_14l,_14y))),e:E(B(_Tn(_14l,_14z))),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_kr),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};case 109:var _154=B(_TP(B(_77(_14z,_14l)),_14S)),_155=_154.c,_156=B(_hb(_155,_10));if(!E(_156)){var _157=B(_Ue(_14l,new T2(0,new T(function(){return E(B(_77(_14y,_14l)).a);}),new T2(1,_14T,_155)),_14y));}else{var _157=B(_Tn(_14l,_14y));}if(!E(_156)){var _158=B(_Ue(_14l,_154.a,_14z));}else{var _158=B(_Tn(_14l,_14z));}return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(B(_Ye(_154.b))),d:E(_157),e:E(_158),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_kr),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};case 114:var _159=B(_77(_YA,_14r)),_15a=B(_77(_Yq,_14r)),_15b=B(_UZ(_15a.a,E(_15a.b),new T(function(){return B(_77(_13E,_14r));}))),_15c=B(_77(_YD,_14r));return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_15a),c:E(_14j),d:E(_14y),e:E(B(_j4(_14f,_14z))),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_kr),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};case 115:var _15d=B(_145(_14o));return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(_14y),e:E(_14z),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};case 116:var _15e=B(_77(_14z,_14l)),_15f=B(_TP(_15e,_14S)),_15g=E(_15f.a);if(!E(_15g)){var _15h=true;}else{var _15h=false;}if(!E(_15h)){var _15i=B(_Ue(_14l,_15g,_14z));}else{var _15i=B(_Ue(_14l,_15e+1|0,_14z));}if(!E(_15h)){var _15j=__Z;}else{var _15j=E(_15f.b);}if(!B(_hb(_15j,_10))){var _15k=B(_14k(_14l,_15j,_14n,_14o,_14p,_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_15i,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q));return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_15k.b),c:E(_15k.c),d:E(_15k.d),e:E(_15k.e),f:E(_15k.f),g:E(_15k.g),h:_15k.h,i:_15k.i,j:_15k.j,k:_15k.k,l:E(_15k.l),m:_15k.m,n:E(_15k.n),o:E(_15k.o),p:E(_15k.p),q:E(_15k.q),r:E(_15k.r),s:E(_15k.s),t:E(_15k.t),u:E(_15k.u),v:_15k.v};}else{return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(_14y),e:E(_15i),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};}break;case 119:var _15l=E(_14e),_15m=E(_14c);return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_Yp),c:E(_149),d:E(_14y),e:E(B(_j4(_14f,_14z))),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_kr),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};default:return {_:0,a:E({_:0,a:E(_14n),b:E(_14o),c:_14p,d:_14q,e:_14r,f:_14s,g:E(B(_y(_14t,_14R))),h:E(_14u),i:E(_14v)}),b:E(_14w),c:E(_14x),d:E(_14y),e:E(_14z),f:E(_14A),g:E(_14B),h:_14C,i:_14D,j:_14E,k:_14F,l:E(_14G),m:_14H,n:E(_14I),o:E(_14J),p:E(_14K),q:E(_14L),r:E(_14M),s:E(_14N),t:E(_14O),u:E(_14P),v:_14Q};}}},_15n=function(_15o,_15p,_15q,_15r,_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M){var _15N=E(_15q);if(!_15N._){return {_:0,a:_15r,b:_15s,c:_15t,d:_15u,e:_15v,f:_15w,g:_15x,h:_15y,i:_15z,j:_15A,k:_15B,l:_15C,m:_15D,n:_15E,o:_15F,p:_15G,q:_15H,r:_15I,s:_15J,t:_15K,u:_15L,v:_15M};}else{var _15O=_15N.b,_15P=E(_15N.a),_15Q=_15P.a,_15R=_15P.b,_15S=function(_15T,_15U,_15V){var _15W=function(_15X,_15Y){if(!B(_hb(_15X,_10))){var _15Z=E(_15r),_160=_15Z.a,_161=_15Z.b,_162=_15Z.c,_163=_15Z.d,_164=_15Z.e,_165=_15Z.f,_166=_15Z.g,_167=_15Z.h,_168=_15Z.i,_169=E(_15X);if(!_169._){return E(_14b);}else{var _16a=_169.b,_16b=E(_169.a),_16c=function(_16d,_16e,_16f,_16g,_16h,_16i,_16j,_16k,_16l,_16m,_16n,_16o,_16p,_16q,_16r,_16s,_16t,_16u,_16v,_16w,_16x,_16y){if(B(_7a(_16h,0))!=B(_7a(_15v,0))){return {_:0,a:_16d,b:_16e,c:_16f,d:_16g,e:_16h,f:_16i,g:_16j,h:_16k,i:_16l,j:_16m,k:_16n,l:_16o,m:_16p,n:_16q,o:_16r,p:_16s,q:_16t,r:_16u,s:_16v,t:_16w,u:_16x,v:_16y};}else{return new F(function(){return _15n(new T(function(){return E(_15o)+1|0;}),_15p,_15O,_16d,_16e,_16f,_16g,_16h,_16i,_16j,_16k,_16l,_16m,_16n,_16o,_16p,_16q,_16r,_16s,_16t,_16u,_16v,_16w,_16x,_16y);});}};switch(E(_16b)){case 97:var _16z=new T(function(){var _16A=E(_16a);if(!_16A._){return E(_14a);}else{return new T2(0,_16A.a,_16A.b);}}),_16B=new T(function(){var _16C=B(_Q5(E(_16z).b));return new T2(0,_16C.a,_16C.b);}),_16D=B(_za(B(_mJ(_Ty,new T(function(){return E(E(_16B).b);})))));if(!_16D._){return E(_TF);}else{if(!E(_16D.b)._){var _16E=new T(function(){var _16F=B(_za(B(_mJ(_Ty,new T(function(){return E(E(_16B).a);})))));if(!_16F._){return E(_TF);}else{if(!E(_16F.b)._){return E(_16F.a);}else{return E(_TE);}}},1),_16G=B(_m9(_16E,E(_16D.a),new T(function(){return E(E(_16z).a);}),_AQ,_161));return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});}else{return E(_TE);}}break;case 104:var _16H=B(_13T(_161));return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});break;case 106:var _16I=B(_za(B(_mJ(_Ty,_16a))));if(!_16I._){return E(_TF);}else{if(!E(_16I.b)._){return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,E(_16I.a),_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});}else{return E(_TE);}}break;case 108:var _16J=E(_15Y);return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,B(_Tn(_16J,_15u)),B(_Tn(_16J,_15v)),_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_kr,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});break;case 109:var _16K=E(_15Y),_16L=B(_TP(B(_77(_15v,_16K)),_16a)),_16M=_16L.c,_16N=B(_hb(_16M,_10));if(!E(_16N)){var _16O=B(_Ue(_16K,new T2(0,new T(function(){return E(B(_77(_15u,_16K)).a);}),new T2(1,_16b,_16M)),_15u));}else{var _16O=B(_Tn(_16K,_15u));}if(!E(_16N)){var _16P=B(_Ue(_16K,_16L.a,_15v));}else{var _16P=B(_Tn(_16K,_15v));}return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,B(_Ye(_16L.b)),_16O,_16P,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_kr,_15H,_15I,_15J,_15K,_15L,_15M);});break;case 114:var _16Q=B(_77(_YA,_164)),_16R=B(_77(_Yq,_164)),_16S=B(_UZ(_16R.a,E(_16R.b),new T(function(){return B(_77(_13E,_164));}))),_16T=B(_77(_YD,_164));return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_16R,E(_14j),_15u,B(_j4(_14f,_15v)),_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_kr,_15H,_15I,_15J,_15K,_15L,_15M);});break;case 115:var _16U=B(_145(_161));return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});break;case 116:var _16V=E(_15Y),_16W=B(_77(_15v,_16V)),_16X=B(_TP(_16W,_16a)),_16Y=E(_16X.a);if(!E(_16Y)){var _16Z=true;}else{var _16Z=false;}if(!E(_16Z)){var _170=B(_Ue(_16V,_16Y,_15v));}else{var _170=B(_Ue(_16V,_16W+1|0,_15v));}if(!E(_16Z)){var _171=__Z;}else{var _171=E(_16X.b);}if(!B(_hb(_171,_10))){var _172=B(_14k(_16V,_171,_160,_161,_162,_163,_164,_165,_166,_167,_168,_15s,_15t,_15u,_170,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M));return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_172.b,_172.c,_172.d,_172.e,_172.f,_172.g,_172.h,_172.i,_172.j,_172.k,_172.l,_172.m,_172.n,_172.o,_172.p,_172.q,_172.r,_172.s,_172.t,_172.u,_172.v);});}else{return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,_15u,_170,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});}break;case 119:var _173=E(_14e),_174=E(_14c);return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_Yp,E(_149),_15u,B(_j4(_14f,_15v)),_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_kr,_15H,_15I,_15J,_15K,_15L,_15M);});break;default:return new F(function(){return _16c({_:0,a:E(_160),b:E(_161),c:_162,d:_163,e:_164,f:_165,g:E(B(_y(_166,_169))),h:E(_167),i:E(_168)},_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});}}}else{return new F(function(){return _15n(new T(function(){return E(_15o)+1|0;}),_15p,_15O,_15r,_15s,_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M);});}},_175=function(_176){if(!B(_4B(_6f,_YC,_15Q))){return new T2(0,_15R,_15o);}else{var _177=function(_178){while(1){var _179=B((function(_17a){var _17b=E(_17a);if(!_17b._){return true;}else{var _17c=_17b.b,_17d=E(_17b.a);if(!_17d._){return E(_YB);}else{switch(E(_17d.a)){case 99:var _17e=E(_15r);if(!E(_17e.i)){return false;}else{var _17f=function(_17g){while(1){var _17h=E(_17g);if(!_17h._){return true;}else{var _17i=_17h.b,_17j=E(_17h.a);if(!_17j._){return E(_YB);}else{if(E(_17j.a)==115){var _17k=B(_za(B(_mJ(_Ty,_17j.b))));if(!_17k._){return E(_TF);}else{if(!E(_17k.b)._){if(_17e.e!=E(_17k.a)){return false;}else{_17g=_17i;continue;}}else{return E(_TE);}}}else{_17g=_17i;continue;}}}}};return new F(function(){return _17f(_17c);});}break;case 115:var _17l=E(_15r),_17m=_17l.e,_17n=B(_za(B(_mJ(_Ty,_17d.b))));if(!_17n._){return E(_TF);}else{if(!E(_17n.b)._){if(_17m!=E(_17n.a)){return false;}else{var _17o=function(_17p){while(1){var _17q=E(_17p);if(!_17q._){return true;}else{var _17r=_17q.b,_17s=E(_17q.a);if(!_17s._){return E(_YB);}else{switch(E(_17s.a)){case 99:if(!E(_17l.i)){return false;}else{_17p=_17r;continue;}break;case 115:var _17t=B(_za(B(_mJ(_Ty,_17s.b))));if(!_17t._){return E(_TF);}else{if(!E(_17t.b)._){if(_17m!=E(_17t.a)){return false;}else{_17p=_17r;continue;}}else{return E(_TE);}}break;default:_17p=_17r;continue;}}}}};return new F(function(){return _17o(_17c);});}}else{return E(_TE);}}break;default:_178=_17c;return __continue;}}}})(_178));if(_179!=__continue){return _179;}}};return (!B(_177(_15V)))?new T2(0,_10,_15o):new T2(0,_15R,_15o);}},_17u=B(_7a(_15p,0))-B(_7a(new T2(1,_15T,_15U),0))|0;if(_17u>0){var _17v=B(_Vg(_17u,_15p));}else{var _17v=E(_15p);}if(E(B(_T5(_15T,_15U,_Dm)))==63){if(!B(_fi(_17v,_10))){var _17w=E(_17v);if(!_17w._){var _17x=E(_Bf);}else{var _17x=B(_Ba(_17w.a,_17w.b));}var _17y=_17x;}else{var _17y=E(_17v);}var _17z=_17y;}else{var _17z=E(_17v);}if(E(B(_Td(_15T,_15U,_Dm)))==63){if(!B(_hb(B(_Ba(_15T,_15U)),_17z))){return new F(function(){return _15W(_10,_15o);});}else{var _17A=B(_175(_));return new F(function(){return _15W(_17A.a,_17A.b);});}}else{if(!B(_hb(new T2(1,_15T,_15U),_17z))){return new F(function(){return _15W(_10,_15o);});}else{var _17B=B(_175(_));return new F(function(){return _15W(_17B.a,_17B.b);});}}},_17C=E(_15Q);if(!_17C._){return E(_Dm);}else{var _17D=_17C.a,_17E=E(_17C.b);if(!_17E._){return new F(function(){return _15S(_17D,_10,_10);});}else{var _17F=E(_17D),_17G=new T(function(){var _17H=B(_ky(38,_17E.a,_17E.b));return new T2(0,_17H.a,_17H.b);});if(E(_17F)==38){return E(_Dm);}else{return new F(function(){return _15S(_17F,new T(function(){return E(E(_17G).a);}),new T(function(){return E(E(_17G).b);}));});}}}}},_17I=function(_17J,_17K){var _17L=new T(function(){var _17M=B(_za(B(_mJ(_Oa,new T(function(){return B(_eI(3,B(_I(0,imul(E(_17K),E(_17J)-1|0)|0,_10))));})))));if(!_17M._){return E(_O9);}else{if(!E(_17M.b)._){return E(_17M.a);}else{return E(_O8);}}});return new T2(0,new T(function(){return B(_Kn(_17L,_17J));}),_17L);},_17N=function(_17O){var _17P=E(_17O);if(!_17P._){return new T2(0,_10,_10);}else{var _17Q=E(_17P.a),_17R=new T(function(){var _17S=B(_17N(_17P.b));return new T2(0,_17S.a,_17S.b);});return new T2(0,new T2(1,_17Q.a,new T(function(){return E(E(_17R).a);})),new T2(1,_17Q.b,new T(function(){return E(E(_17R).b);})));}},_17T=function(_17U){var _17V=E(_17U);switch(_17V){case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;default:if(_17V>>>0>1114111){return new F(function(){return _qY(_17V);});}else{return _17V;}}},_17W=function(_17X,_17Y){while(1){var _17Z=E(_17Y);if(!_17Z._){return __Z;}else{var _180=_17Z.b,_181=E(_17X);if(_181==1){return E(_180);}else{_17X=_181-1|0;_17Y=_180;continue;}}}},_182=function(_183,_184){while(1){var _185=E(_184);if(!_185._){return __Z;}else{var _186=_185.b,_187=E(_183);if(_187==1){return E(_186);}else{_183=_187-1|0;_184=_186;continue;}}}},_188=new T2(1,_5V,_10),_189=64,_18a=new T2(1,_189,_10),_18b=function(_18c,_18d){while(1){var _18e=E(_18c);if(!_18e._){return E(_18d);}else{_18c=_18e.b;_18d=_18e.a;continue;}}},_18f=57,_18g=48,_18h=new T2(1,_189,_10),_18i=new T(function(){return B(err(_mA));}),_18j=new T(function(){return B(err(_my));}),_18k=new T(function(){return B(A3(_yt,_yW,_xY,_z3));}),_18l=function(_18m,_18n){if((_18n-48|0)>>>0>9){var _18o=_18n+_18m|0,_18p=function(_18q){if(!B(_4B(_6f,_18q,_18h))){return E(_18q);}else{return new F(function(){return _18l(_18m,_18q);});}};if(_18o<=122){if(_18o>=97){if(_18o>>>0>1114111){return new F(function(){return _qY(_18o);});}else{return new F(function(){return _18p(_18o);});}}else{if(_18o<=90){if(_18o>>>0>1114111){return new F(function(){return _qY(_18o);});}else{return new F(function(){return _18p(_18o);});}}else{var _18r=65+(_18o-90|0)|0;if(_18r>>>0>1114111){return new F(function(){return _qY(_18r);});}else{return new F(function(){return _18p(_18r);});}}}}else{var _18s=97+(_18o-122|0)|0;if(_18s>>>0>1114111){return new F(function(){return _qY(_18s);});}else{return new F(function(){return _18p(_18s);});}}}else{var _18t=B(_za(B(_mJ(_18k,new T2(1,_18n,_10)))));if(!_18t._){return E(_18j);}else{if(!E(_18t.b)._){var _18u=E(_18t.a)+_18m|0;switch(_18u){case  -1:return E(_18g);case 10:return E(_18f);default:return new F(function(){return _18b(B(_I(0,_18u,_10)),_Dm);});}}else{return E(_18i);}}}},_18v=function(_18w,_18x){if((_18w-48|0)>>>0>9){return _18x;}else{var _18y=B(_za(B(_mJ(_18k,new T2(1,_18w,_10)))));if(!_18y._){return E(_18j);}else{if(!E(_18y.b)._){return new F(function(){return _18l(E(_18y.a),_18x);});}else{return E(_18i);}}}},_18z=function(_18A,_18B){return new F(function(){return _18v(E(_18A),E(_18B));});},_18C=new T2(1,_18z,_10),_18D=5,_18E=new T2(1,_18D,_10),_18F=function(_18G,_18H){return new F(function(){return _77(_18G,E(_18H));});},_18I=function(_18J,_18K,_18L,_18M){return (!B(_hb(_18J,_18L)))?true:(!B(_8f(_18K,_18M)))?true:false;},_18N=function(_18O,_18P){var _18Q=E(_18O),_18R=E(_18P);return new F(function(){return _18I(_18Q.a,_18Q.b,_18R.a,_18R.b);});},_18S=function(_18T,_18U,_18V,_18W){if(!B(_hb(_18T,_18V))){return false;}else{return new F(function(){return _8f(_18U,_18W);});}},_18X=function(_18Y,_18Z){var _190=E(_18Y),_191=E(_18Z);return new F(function(){return _18S(_190.a,_190.b,_191.a,_191.b);});},_192=new T2(0,_18X,_18N),_193=function(_194){var _195=E(_194);if(!_195._){return new T2(0,_10,_10);}else{var _196=E(_195.a),_197=new T(function(){var _198=B(_193(_195.b));return new T2(0,_198.a,_198.b);});return new T2(0,new T2(1,_196.a,new T(function(){return E(E(_197).a);})),new T2(1,_196.b,new T(function(){return E(E(_197).b);})));}},_199=function(_19a){var _19b=E(_19a);if(!_19b._){return new T2(0,_10,_10);}else{var _19c=E(_19b.a),_19d=new T(function(){var _19e=B(_199(_19b.b));return new T2(0,_19e.a,_19e.b);});return new T2(0,new T2(1,_19c.a,new T(function(){return E(E(_19d).a);})),new T2(1,_19c.b,new T(function(){return E(E(_19d).b);})));}},_19f=function(_19g){var _19h=E(_19g);if(!_19h._){return new T2(0,_10,_10);}else{var _19i=E(_19h.a),_19j=new T(function(){var _19k=B(_19f(_19h.b));return new T2(0,_19k.a,_19k.b);});return new T2(0,new T2(1,_19i.a,new T(function(){return E(E(_19j).a);})),new T2(1,_19i.b,new T(function(){return E(E(_19j).b);})));}},_19l=function(_19m,_19n){return (_19m<=_19n)?new T2(1,_19m,new T(function(){return B(_19l(_19m+1|0,_19n));})):__Z;},_19o=new T(function(){return B(_19l(65,90));}),_19p=function(_19q){return (_19q<=122)?new T2(1,_19q,new T(function(){return B(_19p(_19q+1|0));})):E(_19o);},_19r=new T(function(){return B(_19p(97));}),_19s=function(_19t){while(1){var _19u=E(_19t);if(!_19u._){return true;}else{if(!B(_4B(_6f,_19u.a,_19r))){return false;}else{_19t=_19u.b;continue;}}}},_19v=new T(function(){return B(err(_my));}),_19w=new T(function(){return B(err(_mA));}),_19x=new T(function(){return B(A3(_RU,_Sf,_xY,_z3));}),_19y=new T2(0,_10,_10),_19z=new T1(0,0),_19A=new T1(0,2),_19B=new T1(0,1),_19C=new T2(0,_10,_19z),_19D=function(_19E,_19F,_19G){var _19H=new T(function(){var _19I=B(_193(_19F));return new T2(0,_19I.a,_19I.b);}),_19J=new T(function(){return E(E(_19H).b);}),_19K=new T(function(){var _19L=B(_199(E(_19H).a));return new T2(0,_19L.a,_19L.b);}),_19M=new T(function(){return E(E(_19K).b);}),_19N=new T(function(){return E(E(_19K).a);}),_19O=function(_19P){while(1){var _19Q=B((function(_19R){var _19S=E(_19R);if(!_19S._){return __Z;}else{var _19T=_19S.b,_19U=new T(function(){return E(B(_19f(_19S.a)).a);}),_19V=new T(function(){return B(_4B(_6f,_Pz,_19U));}),_19W=new T(function(){if(!E(_19V)){return E(_19y);}else{var _19X=B(_Q5(_19U));return new T2(0,_19X.a,_19X.b);}}),_19Y=new T(function(){return E(E(_19W).a);}),_19Z=new T(function(){return B(_iC(_fq,_19Y,_19N));});if(!B(_4B(_fq,_19Y,_19N))){var _1a0=false;}else{var _1a0=B(_77(_19J,E(_19Z)))==E(_19E);}var _1a1=new T(function(){return E(E(_19W).b);}),_1a2=new T(function(){return B(_iC(_fq,_1a1,_19N));}),_1a3=new T(function(){if(!B(_4B(_fq,_1a1,_19N))){return false;}else{return B(_77(_19J,E(_1a2)))==E(_19E);}}),_1a4=function(_1a5){var _1a6=function(_1a7){return (!E(_1a0))?__Z:(!E(_1a3))?__Z:new T2(1,new T2(0,_19Y,new T(function(){return B(_18F(_19M,_19Z));})),new T2(1,new T2(0,_1a1,new T(function(){return B(_18F(_19M,_1a2));})),_10));};if(!E(_1a0)){if(!E(_1a3)){return new F(function(){return _1a6(_);});}else{return new T2(1,new T2(0,_1a1,new T(function(){return B(_18F(_19M,_1a2));})),_10);}}else{return new F(function(){return _1a6(_);});}};if(!E(_1a0)){var _1a8=B(_1a4(_));}else{if(!E(_1a3)){var _1a9=new T2(1,new T2(0,_19Y,new T(function(){return B(_18F(_19M,_19Z));})),_10);}else{var _1a9=B(_1a4(_));}var _1a8=_1a9;}if(!B(_6E(_192,_1a8,_10))){return new F(function(){return _y(_1a8,new T(function(){return B(_19O(_19T));},1));});}else{if(!E(_19V)){_19P=_19T;return __continue;}else{var _1aa=new T(function(){if(!E(_1a0)){return E(_1a3);}else{return true;}}),_1ab=function(_1ac){return (!B(_19s(_1a1)))?E(_19z):(!E(_1aa))?(!B(_fi(_19Y,_10)))?(!B(_RP(_19Y)))?E(_19z):E(_19A):E(_19z):E(_19z);};if(!B(_19s(_19Y))){var _1ad=B(_1ab(_));}else{if(!E(_1aa)){if(!B(_fi(_1a1,_10))){if(!B(_RP(_1a1))){var _1ae=B(_1ab(_));}else{var _1ae=E(_19B);}var _1af=_1ae;}else{var _1af=B(_1ab(_));}var _1ag=_1af;}else{var _1ag=B(_1ab(_));}var _1ad=_1ag;}if(!B(_8T(_1ad,_19z))){_19P=_19T;return __continue;}else{var _1ah=new T(function(){if(!B(_8f(_1ad,_19B))){if(!B(_8f(_1ad,_19A))){return E(_19C);}else{return new T2(0,_1a1,new T(function(){var _1ai=B(_za(B(_mJ(_19x,_19Y))));if(!_1ai._){return E(_19v);}else{if(!E(_1ai.b)._){return E(_1ai.a);}else{return E(_19w);}}}));}}else{return new T2(0,_19Y,new T(function(){var _1aj=B(_za(B(_mJ(_19x,_1a1))));if(!_1aj._){return E(_19v);}else{if(!E(_1aj.b)._){return E(_1aj.a);}else{return E(_19w);}}}));}});return new T2(1,_1ah,new T(function(){return B(_19O(_19T));}));}}}}})(_19P));if(_19Q!=__continue){return _19Q;}}};return new F(function(){return _19O(_19G);});},_1ak=new T(function(){return B(_a2("Grid.hs:(21,1)-(28,56)|function checkGrid"));}),_1al=function(_1am,_1an){while(1){var _1ao=E(_1an);if(!_1ao._){return false;}else{var _1ap=_1ao.b,_1aq=E(_1am),_1ar=_1aq.a,_1as=_1aq.b,_1at=E(_1ao.a);if(!_1at._){return E(_1ak);}else{var _1au=E(_1at.a),_1av=_1au.a,_1aw=_1au.b,_1ax=E(_1at.b);if(!_1ax._){var _1ay=E(_1ar),_1az=E(_1ay);if(_1az==32){switch(E(_1as)){case 0:if(!E(_1aw)){return true;}else{_1am=new T2(0,_1ay,_AQ);_1an=_1ap;continue;}break;case 1:if(E(_1aw)==1){return true;}else{_1am=new T2(0,_1ay,_YF);_1an=_1ap;continue;}break;case 2:if(E(_1aw)==2){return true;}else{_1am=new T2(0,_1ay,_Zw);_1an=_1ap;continue;}break;case 3:if(E(_1aw)==3){return true;}else{_1am=new T2(0,_1ay,_ZO);_1an=_1ap;continue;}break;case 4:if(E(_1aw)==4){return true;}else{_1am=new T2(0,_1ay,_13I);_1an=_1ap;continue;}break;case 5:if(E(_1aw)==5){return true;}else{_1am=new T2(0,_1ay,_13J);_1an=_1ap;continue;}break;case 6:if(E(_1aw)==6){return true;}else{_1am=new T2(0,_1ay,_13F);_1an=_1ap;continue;}break;case 7:if(E(_1aw)==7){return true;}else{_1am=new T2(0,_1ay,_13G);_1an=_1ap;continue;}break;default:if(E(_1aw)==8){return true;}else{_1am=new T2(0,_1ay,_13H);_1an=_1ap;continue;}}}else{if(_1az!=E(_1av)){_1am=_1aq;_1an=_1ap;continue;}else{switch(E(_1as)){case 0:if(!E(_1aw)){return true;}else{_1am=new T2(0,_1ay,_AQ);_1an=_1ap;continue;}break;case 1:if(E(_1aw)==1){return true;}else{_1am=new T2(0,_1ay,_YF);_1an=_1ap;continue;}break;case 2:if(E(_1aw)==2){return true;}else{_1am=new T2(0,_1ay,_Zw);_1an=_1ap;continue;}break;case 3:if(E(_1aw)==3){return true;}else{_1am=new T2(0,_1ay,_ZO);_1an=_1ap;continue;}break;case 4:if(E(_1aw)==4){return true;}else{_1am=new T2(0,_1ay,_13I);_1an=_1ap;continue;}break;case 5:if(E(_1aw)==5){return true;}else{_1am=new T2(0,_1ay,_13J);_1an=_1ap;continue;}break;case 6:if(E(_1aw)==6){return true;}else{_1am=new T2(0,_1ay,_13F);_1an=_1ap;continue;}break;case 7:if(E(_1aw)==7){return true;}else{_1am=new T2(0,_1ay,_13G);_1an=_1ap;continue;}break;default:if(E(_1aw)==8){return true;}else{_1am=new T2(0,_1ay,_13H);_1an=_1ap;continue;}}}}}else{var _1aA=E(_1ar),_1aB=E(_1aA);if(_1aB==32){switch(E(_1as)){case 0:if(!E(_1aw)){return true;}else{_1am=new T2(0,_1aA,_AQ);_1an=new T2(1,_1ax,_1ap);continue;}break;case 1:if(E(_1aw)==1){return true;}else{_1am=new T2(0,_1aA,_YF);_1an=new T2(1,_1ax,_1ap);continue;}break;case 2:if(E(_1aw)==2){return true;}else{_1am=new T2(0,_1aA,_Zw);_1an=new T2(1,_1ax,_1ap);continue;}break;case 3:if(E(_1aw)==3){return true;}else{_1am=new T2(0,_1aA,_ZO);_1an=new T2(1,_1ax,_1ap);continue;}break;case 4:if(E(_1aw)==4){return true;}else{_1am=new T2(0,_1aA,_13I);_1an=new T2(1,_1ax,_1ap);continue;}break;case 5:if(E(_1aw)==5){return true;}else{_1am=new T2(0,_1aA,_13J);_1an=new T2(1,_1ax,_1ap);continue;}break;case 6:if(E(_1aw)==6){return true;}else{_1am=new T2(0,_1aA,_13F);_1an=new T2(1,_1ax,_1ap);continue;}break;case 7:if(E(_1aw)==7){return true;}else{_1am=new T2(0,_1aA,_13G);_1an=new T2(1,_1ax,_1ap);continue;}break;default:if(E(_1aw)==8){return true;}else{_1am=new T2(0,_1aA,_13H);_1an=new T2(1,_1ax,_1ap);continue;}}}else{if(_1aB!=E(_1av)){_1am=_1aq;_1an=new T2(1,_1ax,_1ap);continue;}else{switch(E(_1as)){case 0:if(!E(_1aw)){return true;}else{_1am=new T2(0,_1aA,_AQ);_1an=new T2(1,_1ax,_1ap);continue;}break;case 1:if(E(_1aw)==1){return true;}else{_1am=new T2(0,_1aA,_YF);_1an=new T2(1,_1ax,_1ap);continue;}break;case 2:if(E(_1aw)==2){return true;}else{_1am=new T2(0,_1aA,_Zw);_1an=new T2(1,_1ax,_1ap);continue;}break;case 3:if(E(_1aw)==3){return true;}else{_1am=new T2(0,_1aA,_ZO);_1an=new T2(1,_1ax,_1ap);continue;}break;case 4:if(E(_1aw)==4){return true;}else{_1am=new T2(0,_1aA,_13I);_1an=new T2(1,_1ax,_1ap);continue;}break;case 5:if(E(_1aw)==5){return true;}else{_1am=new T2(0,_1aA,_13J);_1an=new T2(1,_1ax,_1ap);continue;}break;case 6:if(E(_1aw)==6){return true;}else{_1am=new T2(0,_1aA,_13F);_1an=new T2(1,_1ax,_1ap);continue;}break;case 7:if(E(_1aw)==7){return true;}else{_1am=new T2(0,_1aA,_13G);_1an=new T2(1,_1ax,_1ap);continue;}break;default:if(E(_1aw)==8){return true;}else{_1am=new T2(0,_1aA,_13H);_1an=new T2(1,_1ax,_1ap);continue;}}}}}}}}},_1aC=new T(function(){return B(unCStr("foldr1"));}),_1aD=new T(function(){return B(_dG(_1aC));}),_1aE=function(_1aF,_1aG){var _1aH=E(_1aG);if(!_1aH._){return E(_1aD);}else{var _1aI=_1aH.a,_1aJ=E(_1aH.b);if(!_1aJ._){return E(_1aI);}else{return new F(function(){return A2(_1aF,_1aI,new T(function(){return B(_1aE(_1aF,_1aJ));}));});}}},_1aK=new T(function(){return B(unCStr("\n"));}),_1aL=function(_1aM,_1aN,_){var _1aO=jsWriteHandle(E(_1aM),toJSStr(E(_1aN)));return _7f;},_1aP=function(_1aQ,_1aR,_){var _1aS=E(_1aQ),_1aT=jsWriteHandle(_1aS,toJSStr(E(_1aR)));return new F(function(){return _1aL(_1aS,_1aK,_);});},_1aU=new T1(0,1002),_1aV=new T(function(){return B(unCStr("0.04"));}),_1aW=new T2(0,_1aV,_1aU),_1aX=new T2(0,_1aW,_Yy),_1aY=new T1(0,1000),_1aZ=new T(function(){return B(unCStr("COVID19"));}),_1b0=new T2(0,_1aZ,_1aY),_1b1=new T2(0,_1b0,_Yx),_1b2=new T(function(){return B(unCStr("/P"));}),_1b3=new T2(0,_1b2,_1aY),_1b4=new T2(0,_1b3,_Yx),_1b5=new T1(0,1001),_1b6=new T(function(){return B(unCStr("POSITIVE"));}),_1b7=new T2(0,_1b6,_1b5),_1b8=new T2(0,_1b7,_Yx),_1b9=new T1(0,1003),_1ba=new T(function(){return B(unCStr("N"));}),_1bb=new T2(0,_1ba,_1b9),_1bc=new T2(0,_1bb,_Yx),_1bd=new T2(1,_1bc,_10),_1be=new T(function(){return B(unCStr("CONTACT"));}),_1bf=new T2(0,_1be,_1b9),_1bg=new T2(0,_1bf,_Yx),_1bh=new T2(1,_1bg,_1bd),_1bi=new T(function(){return B(unCStr("H"));}),_1bj=new T2(0,_1bi,_1aU),_1bk=new T2(0,_1bj,_Yx),_1bl=new T2(1,_1bk,_1bh),_1bm=new T(function(){return B(unCStr("VACCINE"));}),_1bn=new T2(0,_1bm,_1aU),_1bo=new T2(0,_1bn,_Yx),_1bp=new T2(1,_1bo,_1bl),_1bq=new T(function(){return B(unCStr("MASK"));}),_1br=new T2(0,_1bq,_1aU),_1bs=new T2(0,_1br,_Yx),_1bt=new T2(1,_1bs,_1bp),_1bu=new T(function(){return B(unCStr("/I"));}),_1bv=new T2(0,_1bu,_1b5),_1bw=new T2(0,_1bv,_Yx),_1bx=new T2(1,_1bw,_1bt),_1by=new T2(1,_1b8,_1bx),_1bz=new T2(1,_1b4,_1by),_1bA=new T2(1,_1b1,_1bz),_1bB=new T2(1,_1aX,_1bA),_1bC=new T(function(){return B(unCStr("Q3"));}),_1bD=new T2(0,_1bC,_1aU),_1bE=new T2(0,_1bD,_Yy),_1bF=new T2(1,_1bE,_1bB),_1bG=new T(function(){return B(unCStr("O"));}),_1bH=new T2(0,_1bG,_1b5),_1bI=new T2(0,_1bH,_Yy),_1bJ=new T2(1,_1bI,_1bF),_1bK=new T(function(){return B(unCStr("Q2"));}),_1bL=new T2(0,_1bK,_1b5),_1bM=new T2(0,_1bL,_Yy),_1bN=new T2(1,_1bM,_1bJ),_1bO=new T(function(){return B(unCStr("H2O"));}),_1bP=new T2(0,_1bO,_1aY),_1bQ=new T2(0,_1bP,_Yy),_1bR=new T2(1,_1bQ,_1bN),_1bS=new T(function(){return B(unCStr("Q1"));}),_1bT=new T2(0,_1bS,_1aY),_1bU=new T2(0,_1bT,_Yy),_1bV=new T2(1,_1bU,_1bR),_1bW=0,_1bX=new T(function(){return B(_UZ(_Yo,5,_Zt));}),_1bY=new T(function(){return B(_77(_em,1));}),_1bZ= -1,_1c0= -2,_1c1=new T(function(){return B(unCStr("I spent a special week"));}),_1c2=14,_1c3=4,_1c4=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1c5=10,_1c6=3,_1c7=new T(function(){return B(unCStr("Coding : yokoP"));}),_1c8=8,_1c9=new T(function(){return B(unCStr("Congratulations!"));}),_1ca=32,_1cb=new T2(0,_1ca,_13J),_1cc=99,_1cd=64,_1ce=new T(function(){return B(_7a(_13E,0));}),_1cf=new T(function(){return B(_77(_em,2));}),_1cg=new T(function(){return B(unCStr("=="));}),_1ch=111,_1ci=112,_1cj=101,_1ck=102,_1cl=new T(function(){var _1cm=E(_YD);if(!_1cm._){return E(_dJ);}else{return E(_1cm.a);}}),_1cn=118,_1co=110,_1cp=98,_1cq=117,_1cr=new T(function(){return B(_a2("CvLoop.hs:(135,9)-(150,75)|function wnMove\'"));}),_1cs=new T(function(){return B(_a2("CvLoop.hs:(120,17)-(124,70)|case"));}),_1ct=new T(function(){return B(unCStr("Thank you for playing!"));}),_1cu=new T(function(){return B(unCStr("choice"));}),_1cv=34,_1cw=new T2(1,_1cv,_10),_1cx=new T(function(){return B(unCStr("ACK"));}),_1cy=new T(function(){return B(unCStr("BEL"));}),_1cz=new T(function(){return B(unCStr("BS"));}),_1cA=new T(function(){return B(unCStr("SP"));}),_1cB=new T2(1,_1cA,_10),_1cC=new T(function(){return B(unCStr("US"));}),_1cD=new T2(1,_1cC,_1cB),_1cE=new T(function(){return B(unCStr("RS"));}),_1cF=new T2(1,_1cE,_1cD),_1cG=new T(function(){return B(unCStr("GS"));}),_1cH=new T2(1,_1cG,_1cF),_1cI=new T(function(){return B(unCStr("FS"));}),_1cJ=new T2(1,_1cI,_1cH),_1cK=new T(function(){return B(unCStr("ESC"));}),_1cL=new T2(1,_1cK,_1cJ),_1cM=new T(function(){return B(unCStr("SUB"));}),_1cN=new T2(1,_1cM,_1cL),_1cO=new T(function(){return B(unCStr("EM"));}),_1cP=new T2(1,_1cO,_1cN),_1cQ=new T(function(){return B(unCStr("CAN"));}),_1cR=new T2(1,_1cQ,_1cP),_1cS=new T(function(){return B(unCStr("ETB"));}),_1cT=new T2(1,_1cS,_1cR),_1cU=new T(function(){return B(unCStr("SYN"));}),_1cV=new T2(1,_1cU,_1cT),_1cW=new T(function(){return B(unCStr("NAK"));}),_1cX=new T2(1,_1cW,_1cV),_1cY=new T(function(){return B(unCStr("DC4"));}),_1cZ=new T2(1,_1cY,_1cX),_1d0=new T(function(){return B(unCStr("DC3"));}),_1d1=new T2(1,_1d0,_1cZ),_1d2=new T(function(){return B(unCStr("DC2"));}),_1d3=new T2(1,_1d2,_1d1),_1d4=new T(function(){return B(unCStr("DC1"));}),_1d5=new T2(1,_1d4,_1d3),_1d6=new T(function(){return B(unCStr("DLE"));}),_1d7=new T2(1,_1d6,_1d5),_1d8=new T(function(){return B(unCStr("SI"));}),_1d9=new T2(1,_1d8,_1d7),_1da=new T(function(){return B(unCStr("SO"));}),_1db=new T2(1,_1da,_1d9),_1dc=new T(function(){return B(unCStr("CR"));}),_1dd=new T2(1,_1dc,_1db),_1de=new T(function(){return B(unCStr("FF"));}),_1df=new T2(1,_1de,_1dd),_1dg=new T(function(){return B(unCStr("VT"));}),_1dh=new T2(1,_1dg,_1df),_1di=new T(function(){return B(unCStr("LF"));}),_1dj=new T2(1,_1di,_1dh),_1dk=new T(function(){return B(unCStr("HT"));}),_1dl=new T2(1,_1dk,_1dj),_1dm=new T2(1,_1cz,_1dl),_1dn=new T2(1,_1cy,_1dm),_1do=new T2(1,_1cx,_1dn),_1dp=new T(function(){return B(unCStr("ENQ"));}),_1dq=new T2(1,_1dp,_1do),_1dr=new T(function(){return B(unCStr("EOT"));}),_1ds=new T2(1,_1dr,_1dq),_1dt=new T(function(){return B(unCStr("ETX"));}),_1du=new T2(1,_1dt,_1ds),_1dv=new T(function(){return B(unCStr("STX"));}),_1dw=new T2(1,_1dv,_1du),_1dx=new T(function(){return B(unCStr("SOH"));}),_1dy=new T2(1,_1dx,_1dw),_1dz=new T(function(){return B(unCStr("NUL"));}),_1dA=new T2(1,_1dz,_1dy),_1dB=92,_1dC=new T(function(){return B(unCStr("\\DEL"));}),_1dD=new T(function(){return B(unCStr("\\a"));}),_1dE=new T(function(){return B(unCStr("\\\\"));}),_1dF=new T(function(){return B(unCStr("\\SO"));}),_1dG=new T(function(){return B(unCStr("\\r"));}),_1dH=new T(function(){return B(unCStr("\\f"));}),_1dI=new T(function(){return B(unCStr("\\v"));}),_1dJ=new T(function(){return B(unCStr("\\n"));}),_1dK=new T(function(){return B(unCStr("\\t"));}),_1dL=new T(function(){return B(unCStr("\\b"));}),_1dM=function(_1dN,_1dO){if(_1dN<=127){var _1dP=E(_1dN);switch(_1dP){case 92:return new F(function(){return _y(_1dE,_1dO);});break;case 127:return new F(function(){return _y(_1dC,_1dO);});break;default:if(_1dP<32){var _1dQ=E(_1dP);switch(_1dQ){case 7:return new F(function(){return _y(_1dD,_1dO);});break;case 8:return new F(function(){return _y(_1dL,_1dO);});break;case 9:return new F(function(){return _y(_1dK,_1dO);});break;case 10:return new F(function(){return _y(_1dJ,_1dO);});break;case 11:return new F(function(){return _y(_1dI,_1dO);});break;case 12:return new F(function(){return _y(_1dH,_1dO);});break;case 13:return new F(function(){return _y(_1dG,_1dO);});break;case 14:return new F(function(){return _y(_1dF,new T(function(){var _1dR=E(_1dO);if(!_1dR._){return __Z;}else{if(E(_1dR.a)==72){return B(unAppCStr("\\&",_1dR));}else{return E(_1dR);}}},1));});break;default:return new F(function(){return _y(new T2(1,_1dB,new T(function(){return B(_77(_1dA,_1dQ));})),_1dO);});}}else{return new T2(1,_1dP,_1dO);}}}else{var _1dS=new T(function(){var _1dT=jsShowI(_1dN);return B(_y(fromJSStr(_1dT),new T(function(){var _1dU=E(_1dO);if(!_1dU._){return __Z;}else{var _1dV=E(_1dU.a);if(_1dV<48){return E(_1dU);}else{if(_1dV>57){return E(_1dU);}else{return B(unAppCStr("\\&",_1dU));}}}},1)));});return new T2(1,_1dB,_1dS);}},_1dW=new T(function(){return B(unCStr("\\\""));}),_1dX=function(_1dY,_1dZ){var _1e0=E(_1dY);if(!_1e0._){return E(_1dZ);}else{var _1e1=_1e0.b,_1e2=E(_1e0.a);if(_1e2==34){return new F(function(){return _y(_1dW,new T(function(){return B(_1dX(_1e1,_1dZ));},1));});}else{return new F(function(){return _1dM(_1e2,new T(function(){return B(_1dX(_1e1,_1dZ));}));});}}},_1e3=new T(function(){return B(_1dX(_1cu,_1cw));}),_1e4=new T2(1,_1cv,_1e3),_1e5=new T(function(){return B(unAppCStr("[]",_10));}),_1e6=new T2(1,_1cv,_10),_1e7=17,_1e8=2,_1e9=new T(function(){return B(unCStr("10/18 to 10/25 in 2021"));}),_1ea=15,_1eb=5,_1ec=new T2(1,_2B,_10),_1ed=function(_1ee,_1ef){return new T2(1,_1cv,new T(function(){return B(_1dX(_1ee,new T2(1,_1cv,_1ef)));}));},_1eg=function(_1eh){var _1ei=E(_1eh);if(!_1ei._){return E(_1ec);}else{var _1ej=new T(function(){var _1ek=E(_1ei.a),_1el=new T(function(){return B(A3(_1aE,_6R,new T2(1,function(_1em){return new F(function(){return _1ed(_1ek.a,_1em);});},new T2(1,function(_1en){return new F(function(){return _1ed(_1ek.b,_1en);});},_10)),new T2(1,_G,new T(function(){return B(_1eg(_1ei.b));}))));});return new T2(1,_H,_1el);});return new T2(1,_2A,_1ej);}},_1eo=function(_1ep){var _1eq=E(_1ep);if(!_1eq._){return E(_1ec);}else{var _1er=new T(function(){return B(_I(0,E(_1eq.a),new T(function(){return B(_1eo(_1eq.b));})));});return new T2(1,_2A,_1er);}},_1es=function(_1et){var _1eu=E(_1et);if(!_1eu._){return E(_1ec);}else{var _1ev=new T(function(){var _1ew=E(_1eu.a),_1ex=new T(function(){return B(A3(_1aE,_6R,new T2(1,function(_1ey){return new F(function(){return _1ed(_1ew.a,_1ey);});},new T2(1,function(_1ez){return new F(function(){return _1ed(_1ew.b,_1ez);});},_10)),new T2(1,_G,new T(function(){return B(_1es(_1eu.b));}))));});return new T2(1,_H,_1ex);});return new T2(1,_2A,_1ev);}},_1eA=new T(function(){return B(unCStr("True"));}),_1eB=new T(function(){return B(unCStr("False"));}),_1eC=function(_){return new F(function(){return jsMkStdout();});},_1eD=new T(function(){return B(_3(_1eC));}),_1eE=function(_1eF,_1eG,_1eH,_1eI,_1eJ,_1eK,_1eL,_1eM,_1eN,_1eO,_1eP,_1eQ,_1eR,_1eS,_1eT,_1eU,_1eV,_1eW,_1eX,_1eY,_1eZ,_1f0,_1f1,_1f2,_1f3,_1f4,_1f5,_1f6,_1f7,_1f8,_1f9,_1fa,_1fb,_1fc,_){var _1fd=new T2(0,_1eW,_1eX),_1fe=new T2(0,_1eQ,_1eR),_1ff={_:0,a:E(_1eH),b:E(_1eI),c:_1eJ,d:_1eK,e:_1eL,f:_1eM,g:E(_1eN),h:E(_1eO),i:E(_1eP)};if(!E(_1f9)){var _1fg=function(_1fh){if(!E(_1f7)){var _1fi=function(_){var _1fj=function(_){var _1fk=function(_){var _1fl=B(_1aP(_1eD,new T2(1,_1cv,new T(function(){return B(_1dX(_1eN,_1e6));})),_)),_1fm=function(_){var _1fn=function(_){var _1fo=B(_Pa(_1eb,_1eM,_)),_1fp=E(_1eF),_1fq=_1fp.a,_1fr=_1fp.b,_1fs=new T(function(){return B(_17T(E(_1eG)));}),_1ft=new T(function(){var _1fu=function(_1fv,_1fw){var _1fx=E(_1fv),_1fy=B(_77(B(_77(_1eI,_1fw)),_1fx)),_1fz=_1fy.a,_1fA=_1fy.b;if(E(_1eK)==32){if(!B(_4B(_6f,_1fz,_18a))){var _1fB=false;}else{switch(E(_1fA)){case 0:var _1fC=true;break;case 1:var _1fC=false;break;case 2:var _1fC=false;break;case 3:var _1fC=false;break;case 4:var _1fC=false;break;case 5:var _1fC=false;break;case 6:var _1fC=false;break;case 7:var _1fC=false;break;default:var _1fC=false;}var _1fB=_1fC;}var _1fD=_1fB;}else{var _1fD=false;}if(E(_1eK)==32){if(E(_1fz)==32){var _1fE=false;}else{switch(E(_1fA)){case 0:if(!E(_1fD)){var _1fF=true;}else{var _1fF=false;}var _1fG=_1fF;break;case 1:var _1fG=false;break;case 2:var _1fG=false;break;case 3:var _1fG=false;break;case 4:var _1fG=false;break;case 5:var _1fG=false;break;case 6:var _1fG=false;break;case 7:var _1fG=false;break;default:if(!E(_1fD)){var _1fH=true;}else{var _1fH=false;}var _1fG=_1fH;}var _1fE=_1fG;}var _1fI=_1fE;}else{var _1fI=false;}var _1fJ=new T(function(){return B(_m9(_1fx,_1fw,new T(function(){if(!E(_1fI)){if(!E(_1fD)){return E(_1fz);}else{return _1eJ;}}else{return E(_1ca);}}),_1fA,_1eI));});switch(E(_1fA)){case 3:var _1fK=true;break;case 4:if(E(_1eK)==32){var _1fL=true;}else{var _1fL=false;}var _1fK=_1fL;break;default:var _1fK=false;}if(!E(_1fK)){var _1fM=E(_1fJ);}else{var _1fN=E(_1eH),_1fO=E(_1fN.a),_1fP=new T(function(){return B(_77(_1fJ,_1fw));}),_1fQ=function(_1fR,_1fS){var _1fT=E(_1fR);if(_1fT==( -1)){return E(_1fJ);}else{var _1fU=new T(function(){return B(_m9(_1fx,_1fw,_1ca,_AQ,_1fJ));}),_1fV=E(_1fS);if(_1fV==( -1)){var _1fW=__Z;}else{var _1fW=B(_77(_1fU,_1fV));}if(E(B(_77(_1fW,_1fT)).a)==32){var _1fX=new T(function(){var _1fY=new T(function(){return B(_77(_1fP,_1fx));}),_1fZ=new T2(1,new T2(0,new T(function(){return E(E(_1fY).a);}),new T(function(){return E(E(_1fY).b);})),new T(function(){var _1g0=_1fT+1|0;if(_1g0>0){return B(_17W(_1g0,_1fW));}else{return E(_1fW);}}));if(0>=_1fT){return E(_1fZ);}else{var _1g1=function(_1g2,_1g3){var _1g4=E(_1g2);if(!_1g4._){return E(_1fZ);}else{var _1g5=_1g4.a,_1g6=E(_1g3);return (_1g6==1)?new T2(1,_1g5,_1fZ):new T2(1,_1g5,new T(function(){return B(_1g1(_1g4.b,_1g6-1|0));}));}};return B(_1g1(_1fW,_1fT));}}),_1g7=new T2(1,_1fX,new T(function(){var _1g8=_1fS+1|0;if(_1g8>0){return B(_182(_1g8,_1fU));}else{return E(_1fU);}}));if(0>=_1fS){return E(_1g7);}else{var _1g9=function(_1ga,_1gb){var _1gc=E(_1ga);if(!_1gc._){return E(_1g7);}else{var _1gd=_1gc.a,_1ge=E(_1gb);return (_1ge==1)?new T2(1,_1gd,_1g7):new T2(1,_1gd,new T(function(){return B(_1g9(_1gc.b,_1ge-1|0));}));}};return new F(function(){return _1g9(_1fU,_1fS);});}}else{return E(_1fJ);}}};if(_1fx<=_1fO){if(_1fO<=_1fx){var _1gf=E(_1fN.b);if(_1fw<=_1gf){if(_1gf<=_1fw){var _1gg=E(_1cs);}else{var _1gh=E(_1fw);if(!_1gh){var _1gi=B(_1fQ( -1, -1));}else{var _1gi=B(_1fQ(_1fx,_1gh-1|0));}var _1gg=_1gi;}var _1gj=_1gg;}else{if(_1fw!=(B(_7a(_1fJ,0))-1|0)){var _1gk=B(_1fQ(_1fx,_1fw+1|0));}else{var _1gk=B(_1fQ( -1, -1));}var _1gj=_1gk;}var _1gl=_1gj;}else{var _1gm=E(_1fx);if(!_1gm){var _1gn=B(_1fQ( -1, -1));}else{var _1gn=B(_1fQ(_1gm-1|0,_1fw));}var _1gl=_1gn;}var _1go=_1gl;}else{if(_1fx!=(B(_7a(_1fP,0))-1|0)){var _1gp=B(_1fQ(_1fx+1|0,_1fw));}else{var _1gp=B(_1fQ( -1, -1));}var _1go=_1gp;}var _1fM=_1go;}if(!E(_1eO)){var _1gq=E(_1fM);}else{var _1gr=new T(function(){var _1gs=E(_1fM);if(!_1gs._){return E(_dJ);}else{return B(_7a(_1gs.a,0));}}),_1gt=new T(function(){return B(_7a(_1fM,0));}),_1gu=function(_1gv,_1gw,_1gx,_1gy,_1gz,_1gA,_1gB){while(1){var _1gC=B((function(_1gD,_1gE,_1gF,_1gG,_1gH,_1gI,_1gJ){var _1gK=E(_1gJ);if(!_1gK._){return E(_1gG);}else{var _1gL=_1gK.b,_1gM=E(_1gK.a);if(!_1gM._){return E(_1cr);}else{var _1gN=_1gM.b,_1gO=E(_1gM.a);if(E(_1gO.b)==5){var _1gP=new T(function(){var _1gQ=B(_17I(_1eb,_1gD));return new T2(0,_1gQ.a,_1gQ.b);}),_1gR=new T(function(){var _1gS=function(_1gT,_1gU){var _1gV=function(_1gW){return new F(function(){return _m9(_1gE,_1gF,_1ca,_AQ,new T(function(){return B(_m9(_1gT,E(_1gU),_1gO.a,_13J,_1gG));}));});};if(_1gT!=_1gE){return new F(function(){return _1gV(_);});}else{if(E(_1gU)!=_1gF){return new F(function(){return _1gV(_);});}else{return E(_1gG);}}};switch(E(E(_1gP).a)){case 1:var _1gX=_1gE-1|0;if(_1gX<0){return B(_1gS(_1gE,_1gF));}else{if(_1gX>=E(_1gr)){return B(_1gS(_1gE,_1gF));}else{if(_1gF<0){return B(_1gS(_1gE,_1gF));}else{if(_1gF>=E(_1gt)){return B(_1gS(_1gE,_1gF));}else{if(_1gX!=_1gH){if(E(B(_77(B(_77(_1gG,_1gF)),_1gX)).a)==32){return B(_1gS(_1gX,_1gF));}else{return B(_1gS(_1gE,_1gF));}}else{if(_1gF!=_1gI){if(E(B(_77(B(_77(_1gG,_1gF)),_1gX)).a)==32){return B(_1gS(_1gX,_1gF));}else{return B(_1gS(_1gE,_1gF));}}else{return B(_1gS(_1gE,_1gF));}}}}}}break;case 2:if(_1gE<0){return B(_1gS(_1gE,_1gF));}else{if(_1gE>=E(_1gr)){return B(_1gS(_1gE,_1gF));}else{var _1gY=_1gF-1|0;if(_1gY<0){return B(_1gS(_1gE,_1gF));}else{if(_1gY>=E(_1gt)){return B(_1gS(_1gE,_1gF));}else{if(_1gE!=_1gH){if(E(B(_77(B(_77(_1gG,_1gY)),_1gE)).a)==32){return B(_1gS(_1gE,_1gY));}else{return B(_1gS(_1gE,_1gF));}}else{if(_1gY!=_1gI){if(E(B(_77(B(_77(_1gG,_1gY)),_1gE)).a)==32){return B(_1gS(_1gE,_1gY));}else{return B(_1gS(_1gE,_1gF));}}else{return B(_1gS(_1gE,_1gF));}}}}}}break;case 3:var _1gZ=_1gE+1|0;if(_1gZ<0){return B(_1gS(_1gE,_1gF));}else{if(_1gZ>=E(_1gr)){return B(_1gS(_1gE,_1gF));}else{if(_1gF<0){return B(_1gS(_1gE,_1gF));}else{if(_1gF>=E(_1gt)){return B(_1gS(_1gE,_1gF));}else{if(_1gZ!=_1gH){if(E(B(_77(B(_77(_1gG,_1gF)),_1gZ)).a)==32){return B(_1gS(_1gZ,_1gF));}else{return B(_1gS(_1gE,_1gF));}}else{if(_1gF!=_1gI){if(E(B(_77(B(_77(_1gG,_1gF)),_1gZ)).a)==32){return B(_1gS(_1gZ,_1gF));}else{return B(_1gS(_1gE,_1gF));}}else{return B(_1gS(_1gE,_1gF));}}}}}}break;case 4:if(_1gE<0){return B(_1gS(_1gE,_1gF));}else{if(_1gE>=E(_1gr)){return B(_1gS(_1gE,_1gF));}else{var _1h0=_1gF+1|0;if(_1h0<0){return B(_1gS(_1gE,_1gF));}else{if(_1h0>=E(_1gt)){return B(_1gS(_1gE,_1gF));}else{if(_1gE!=_1gH){if(E(B(_77(B(_77(_1gG,_1h0)),_1gE)).a)==32){return B(_1gS(_1gE,_1h0));}else{return B(_1gS(_1gE,_1gF));}}else{if(_1h0!=_1gI){if(E(B(_77(B(_77(_1gG,_1h0)),_1gE)).a)==32){return B(_1gS(_1gE,_1h0));}else{return B(_1gS(_1gE,_1gF));}}else{return B(_1gS(_1gE,_1gF));}}}}}}break;default:if(_1gE<0){return B(_1gS(_1gE,_1gF));}else{if(_1gE>=E(_1gr)){return B(_1gS(_1gE,_1gF));}else{if(_1gF<0){return B(_1gS(_1gE,_1gF));}else{if(_1gF>=E(_1gt)){return B(_1gS(_1gE,_1gF));}else{if(_1gE!=_1gH){var _1h1=E(B(_77(B(_77(_1gG,_1gF)),_1gE)).a);return B(_1gS(_1gE,_1gF));}else{if(_1gF!=_1gI){var _1h2=E(B(_77(B(_77(_1gG,_1gF)),_1gE)).a);return B(_1gS(_1gE,_1gF));}else{return B(_1gS(_1gE,_1gF));}}}}}}}}),_1h3=E(_1gN);if(!_1h3._){var _1h4=_1gF+1|0,_1h5=_1gH,_1h6=_1gI;_1gv=new T(function(){return E(E(_1gP).b);},1);_1gw=0;_1gx=_1h4;_1gy=_1gR;_1gz=_1h5;_1gA=_1h6;_1gB=_1gL;return __continue;}else{var _1h7=_1gE+1|0,_1h4=_1gF,_1h5=_1gH,_1h6=_1gI;_1gv=new T(function(){return E(E(_1gP).b);},1);_1gw=_1h7;_1gx=_1h4;_1gy=_1gR;_1gz=_1h5;_1gA=_1h6;_1gB=new T2(1,_1h3,_1gL);return __continue;}}else{var _1h8=E(_1gN);if(!_1h8._){var _1h9=_1gD,_1h4=_1gF+1|0,_1ha=_1gG,_1h5=_1gH,_1h6=_1gI;_1gv=_1h9;_1gw=0;_1gx=_1h4;_1gy=_1ha;_1gz=_1h5;_1gA=_1h6;_1gB=_1gL;return __continue;}else{var _1h9=_1gD,_1h7=_1gE+1|0,_1h4=_1gF,_1ha=_1gG,_1h5=_1gH,_1h6=_1gI;_1gv=_1h9;_1gw=_1h7;_1gx=_1h4;_1gy=_1ha;_1gz=_1h5;_1gA=_1h6;_1gB=new T2(1,_1h8,_1gL);return __continue;}}}}})(_1gv,_1gw,_1gx,_1gy,_1gz,_1gA,_1gB));if(_1gC!=__continue){return _1gC;}}},_1gq=B(_1gu(_1eM,0,0,_1fM,_1fx,_1fw,_1fM));}var _1hb=function(_1hc){var _1hd=function(_1he){var _1hf=new T(function(){switch(E(_1fA)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1hg=new T(function(){if(!E(_1fK)){if(!E(_1hf)){return new T2(0,_1fx,_1fw);}else{return E(_1eH);}}else{if(!B(_6E(_6Q,_1gq,_1fJ))){if(!E(_1hf)){return new T2(0,_1fx,_1fw);}else{return E(_1eH);}}else{return E(_1eH);}}}),_1hh=new T(function(){return E(E(_1hg).b);}),_1hi=new T(function(){return E(E(_1hg).a);});if(!E(_1fK)){var _1hj=E(_1eP);}else{var _1hj=E(B(_SK(new T(function(){return B(_19D(_1eL,_1bV,_1gq));}),_1gq)).a);}var _1hk=new T(function(){if(!E(_1fI)){if(!E(_1fD)){var _1hl=function(_1hm){var _1hn=function(_1ho){var _1hp=E(_1fA);if(_1hp==4){return new T2(1,_1co,new T2(1,_1fz,_10));}else{if(!E(_1hf)){return (E(_1hp)==2)?new T2(1,_1cq,new T2(1,_1fz,_10)):__Z;}else{var _1hq=E(_1fz);return (E(_1hq)==61)?new T2(1,_1cp,new T2(1,_1hq,new T(function(){return B(_I(0,_1fw,_10));}))):new T2(1,_1cp,new T2(1,_1hq,_10));}}};if(!E(_1fK)){return new F(function(){return _1hn(_);});}else{var _1hr=E(_1eH);if(E(_1hr.a)!=E(_1hi)){return new T2(1,_1cn,new T2(1,_1fz,_10));}else{if(E(_1hr.b)!=E(_1hh)){return new T2(1,_1cn,new T2(1,_1fz,_10));}else{return new F(function(){return _1hn(_);});}}}};if(!E(_1fK)){return B(_1hl(_));}else{if(!E(_1hj)){return B(_1hl(_));}else{return E(_1cg);}}}else{return new T2(1,_1ck,new T2(1,_1fz,_10));}}else{return new T2(1,_1cj,new T2(1,_1fz,_10));}},1);return {_:0,a:new T2(0,_1hi,_1hh),b:_1gq,c:_1hc,d:_1he,e:_1eL,f:_1eM,g:B(_y(_1eN,_1hk)),h:_1eO,i:E(_1hj)};};if(!E(_1fI)){return new F(function(){return _1hd(_1eK);});}else{return new F(function(){return _1hd(E(_1fz));});}};if(!E(_1fD)){var _1hs=B(_1hb(_1eJ));return {_:0,a:E(_1hs.a),b:E(_1hs.b),c:_1hs.c,d:_1hs.d,e:_1hs.e,f:_1hs.f,g:E(_1hs.g),h:E(_1hs.h),i:E(_1hs.i)};}else{var _1ht=B(_1hb(E(_1fz)));return {_:0,a:E(_1ht.a),b:E(_1ht.b),c:_1ht.c,d:_1ht.d,e:_1ht.e,f:_1ht.f,g:E(_1ht.g),h:E(_1ht.h),i:E(_1ht.i)};}},_1hu=function(_1hv,_1hw){var _1hx=E(_1hw),_1hy=B(_77(B(_77(_1eI,_1hx)),_1hv)),_1hz=_1hy.a,_1hA=_1hy.b;if(E(_1eK)==32){if(!B(_4B(_6f,_1hz,_18a))){var _1hB=false;}else{switch(E(_1hA)){case 0:var _1hC=true;break;case 1:var _1hC=false;break;case 2:var _1hC=false;break;case 3:var _1hC=false;break;case 4:var _1hC=false;break;case 5:var _1hC=false;break;case 6:var _1hC=false;break;case 7:var _1hC=false;break;default:var _1hC=false;}var _1hB=_1hC;}var _1hD=_1hB;}else{var _1hD=false;}if(E(_1eK)==32){if(E(_1hz)==32){var _1hE=false;}else{switch(E(_1hA)){case 0:if(!E(_1hD)){var _1hF=true;}else{var _1hF=false;}var _1hG=_1hF;break;case 1:var _1hG=false;break;case 2:var _1hG=false;break;case 3:var _1hG=false;break;case 4:var _1hG=false;break;case 5:var _1hG=false;break;case 6:var _1hG=false;break;case 7:var _1hG=false;break;default:if(!E(_1hD)){var _1hH=true;}else{var _1hH=false;}var _1hG=_1hH;}var _1hE=_1hG;}var _1hI=_1hE;}else{var _1hI=false;}var _1hJ=new T(function(){return B(_m9(_1hv,_1hx,new T(function(){if(!E(_1hI)){if(!E(_1hD)){return E(_1hz);}else{return _1eJ;}}else{return E(_1ca);}}),_1hA,_1eI));});switch(E(_1hA)){case 3:var _1hK=true;break;case 4:if(E(_1eK)==32){var _1hL=true;}else{var _1hL=false;}var _1hK=_1hL;break;default:var _1hK=false;}if(!E(_1hK)){var _1hM=E(_1hJ);}else{var _1hN=E(_1eH),_1hO=E(_1hN.a),_1hP=new T(function(){return B(_77(_1hJ,_1hx));}),_1hQ=function(_1hR,_1hS){var _1hT=E(_1hR);if(_1hT==( -1)){return E(_1hJ);}else{var _1hU=new T(function(){return B(_m9(_1hv,_1hx,_1ca,_AQ,_1hJ));}),_1hV=E(_1hS);if(_1hV==( -1)){var _1hW=__Z;}else{var _1hW=B(_77(_1hU,_1hV));}if(E(B(_77(_1hW,_1hT)).a)==32){var _1hX=new T(function(){var _1hY=new T(function(){return B(_77(_1hP,_1hv));}),_1hZ=new T2(1,new T2(0,new T(function(){return E(E(_1hY).a);}),new T(function(){return E(E(_1hY).b);})),new T(function(){var _1i0=_1hT+1|0;if(_1i0>0){return B(_17W(_1i0,_1hW));}else{return E(_1hW);}}));if(0>=_1hT){return E(_1hZ);}else{var _1i1=function(_1i2,_1i3){var _1i4=E(_1i2);if(!_1i4._){return E(_1hZ);}else{var _1i5=_1i4.a,_1i6=E(_1i3);return (_1i6==1)?new T2(1,_1i5,_1hZ):new T2(1,_1i5,new T(function(){return B(_1i1(_1i4.b,_1i6-1|0));}));}};return B(_1i1(_1hW,_1hT));}}),_1i7=new T2(1,_1hX,new T(function(){var _1i8=_1hS+1|0;if(_1i8>0){return B(_182(_1i8,_1hU));}else{return E(_1hU);}}));if(0>=_1hS){return E(_1i7);}else{var _1i9=function(_1ia,_1ib){var _1ic=E(_1ia);if(!_1ic._){return E(_1i7);}else{var _1id=_1ic.a,_1ie=E(_1ib);return (_1ie==1)?new T2(1,_1id,_1i7):new T2(1,_1id,new T(function(){return B(_1i9(_1ic.b,_1ie-1|0));}));}};return new F(function(){return _1i9(_1hU,_1hS);});}}else{return E(_1hJ);}}};if(_1hv<=_1hO){if(_1hO<=_1hv){var _1if=E(_1hN.b);if(_1hx<=_1if){if(_1if<=_1hx){var _1ig=E(_1cs);}else{var _1ih=E(_1hx);if(!_1ih){var _1ii=B(_1hQ( -1, -1));}else{var _1ii=B(_1hQ(_1hv,_1ih-1|0));}var _1ig=_1ii;}var _1ij=_1ig;}else{if(_1hx!=(B(_7a(_1hJ,0))-1|0)){var _1ik=B(_1hQ(_1hv,_1hx+1|0));}else{var _1ik=B(_1hQ( -1, -1));}var _1ij=_1ik;}var _1il=_1ij;}else{var _1im=E(_1hv);if(!_1im){var _1in=B(_1hQ( -1, -1));}else{var _1in=B(_1hQ(_1im-1|0,_1hx));}var _1il=_1in;}var _1io=_1il;}else{if(_1hv!=(B(_7a(_1hP,0))-1|0)){var _1ip=B(_1hQ(_1hv+1|0,_1hx));}else{var _1ip=B(_1hQ( -1, -1));}var _1io=_1ip;}var _1hM=_1io;}if(!E(_1eO)){var _1iq=E(_1hM);}else{var _1ir=new T(function(){var _1is=E(_1hM);if(!_1is._){return E(_dJ);}else{return B(_7a(_1is.a,0));}}),_1it=new T(function(){return B(_7a(_1hM,0));}),_1iu=function(_1iv,_1iw,_1ix,_1iy,_1iz,_1iA,_1iB){while(1){var _1iC=B((function(_1iD,_1iE,_1iF,_1iG,_1iH,_1iI,_1iJ){var _1iK=E(_1iJ);if(!_1iK._){return E(_1iG);}else{var _1iL=_1iK.b,_1iM=E(_1iK.a);if(!_1iM._){return E(_1cr);}else{var _1iN=_1iM.b,_1iO=E(_1iM.a);if(E(_1iO.b)==5){var _1iP=new T(function(){var _1iQ=B(_17I(_1eb,_1iD));return new T2(0,_1iQ.a,_1iQ.b);}),_1iR=new T(function(){var _1iS=function(_1iT,_1iU){var _1iV=function(_1iW){return new F(function(){return _m9(_1iE,_1iF,_1ca,_AQ,new T(function(){return B(_m9(_1iT,E(_1iU),_1iO.a,_13J,_1iG));}));});};if(_1iT!=_1iE){return new F(function(){return _1iV(_);});}else{if(E(_1iU)!=_1iF){return new F(function(){return _1iV(_);});}else{return E(_1iG);}}};switch(E(E(_1iP).a)){case 1:var _1iX=_1iE-1|0;if(_1iX<0){return B(_1iS(_1iE,_1iF));}else{if(_1iX>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{if(_1iF<0){return B(_1iS(_1iE,_1iF));}else{if(_1iF>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iX!=_1iH){if(E(B(_77(B(_77(_1iG,_1iF)),_1iX)).a)==32){return B(_1iS(_1iX,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1iF!=_1iI){if(E(B(_77(B(_77(_1iG,_1iF)),_1iX)).a)==32){return B(_1iS(_1iX,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;case 2:if(_1iE<0){return B(_1iS(_1iE,_1iF));}else{if(_1iE>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{var _1iY=_1iF-1|0;if(_1iY<0){return B(_1iS(_1iE,_1iF));}else{if(_1iY>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iE!=_1iH){if(E(B(_77(B(_77(_1iG,_1iY)),_1iE)).a)==32){return B(_1iS(_1iE,_1iY));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1iY!=_1iI){if(E(B(_77(B(_77(_1iG,_1iY)),_1iE)).a)==32){return B(_1iS(_1iE,_1iY));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;case 3:var _1iZ=_1iE+1|0;if(_1iZ<0){return B(_1iS(_1iE,_1iF));}else{if(_1iZ>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{if(_1iF<0){return B(_1iS(_1iE,_1iF));}else{if(_1iF>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iZ!=_1iH){if(E(B(_77(B(_77(_1iG,_1iF)),_1iZ)).a)==32){return B(_1iS(_1iZ,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1iF!=_1iI){if(E(B(_77(B(_77(_1iG,_1iF)),_1iZ)).a)==32){return B(_1iS(_1iZ,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;case 4:if(_1iE<0){return B(_1iS(_1iE,_1iF));}else{if(_1iE>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{var _1j0=_1iF+1|0;if(_1j0<0){return B(_1iS(_1iE,_1iF));}else{if(_1j0>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iE!=_1iH){if(E(B(_77(B(_77(_1iG,_1j0)),_1iE)).a)==32){return B(_1iS(_1iE,_1j0));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1j0!=_1iI){if(E(B(_77(B(_77(_1iG,_1j0)),_1iE)).a)==32){return B(_1iS(_1iE,_1j0));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;default:if(_1iE<0){return B(_1iS(_1iE,_1iF));}else{if(_1iE>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{if(_1iF<0){return B(_1iS(_1iE,_1iF));}else{if(_1iF>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iE!=_1iH){var _1j1=E(B(_77(B(_77(_1iG,_1iF)),_1iE)).a);return B(_1iS(_1iE,_1iF));}else{if(_1iF!=_1iI){var _1j2=E(B(_77(B(_77(_1iG,_1iF)),_1iE)).a);return B(_1iS(_1iE,_1iF));}else{return B(_1iS(_1iE,_1iF));}}}}}}}}),_1j3=E(_1iN);if(!_1j3._){var _1j4=_1iF+1|0,_1j5=_1iH,_1j6=_1iI;_1iv=new T(function(){return E(E(_1iP).b);},1);_1iw=0;_1ix=_1j4;_1iy=_1iR;_1iz=_1j5;_1iA=_1j6;_1iB=_1iL;return __continue;}else{var _1j7=_1iE+1|0,_1j4=_1iF,_1j5=_1iH,_1j6=_1iI;_1iv=new T(function(){return E(E(_1iP).b);},1);_1iw=_1j7;_1ix=_1j4;_1iy=_1iR;_1iz=_1j5;_1iA=_1j6;_1iB=new T2(1,_1j3,_1iL);return __continue;}}else{var _1j8=E(_1iN);if(!_1j8._){var _1j9=_1iD,_1j4=_1iF+1|0,_1ja=_1iG,_1j5=_1iH,_1j6=_1iI;_1iv=_1j9;_1iw=0;_1ix=_1j4;_1iy=_1ja;_1iz=_1j5;_1iA=_1j6;_1iB=_1iL;return __continue;}else{var _1j9=_1iD,_1j7=_1iE+1|0,_1j4=_1iF,_1ja=_1iG,_1j5=_1iH,_1j6=_1iI;_1iv=_1j9;_1iw=_1j7;_1ix=_1j4;_1iy=_1ja;_1iz=_1j5;_1iA=_1j6;_1iB=new T2(1,_1j8,_1iL);return __continue;}}}}})(_1iv,_1iw,_1ix,_1iy,_1iz,_1iA,_1iB));if(_1iC!=__continue){return _1iC;}}},_1iq=B(_1iu(_1eM,0,0,_1hM,_1hv,_1hx,_1hM));}var _1jb=function(_1jc){var _1jd=function(_1je){var _1jf=new T(function(){switch(E(_1hA)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1jg=new T(function(){if(!E(_1hK)){if(!E(_1jf)){return new T2(0,_1hv,_1hx);}else{return E(_1eH);}}else{if(!B(_6E(_6Q,_1iq,_1hJ))){if(!E(_1jf)){return new T2(0,_1hv,_1hx);}else{return E(_1eH);}}else{return E(_1eH);}}}),_1jh=new T(function(){return E(E(_1jg).b);}),_1ji=new T(function(){return E(E(_1jg).a);});if(!E(_1hK)){var _1jj=E(_1eP);}else{var _1jj=E(B(_SK(new T(function(){return B(_19D(_1eL,_1bV,_1iq));}),_1iq)).a);}var _1jk=new T(function(){if(!E(_1hI)){if(!E(_1hD)){var _1jl=function(_1jm){var _1jn=function(_1jo){var _1jp=E(_1hA);if(_1jp==4){return new T2(1,_1co,new T2(1,_1hz,_10));}else{if(!E(_1jf)){return (E(_1jp)==2)?new T2(1,_1cq,new T2(1,_1hz,_10)):__Z;}else{var _1jq=E(_1hz);return (E(_1jq)==61)?new T2(1,_1cp,new T2(1,_1jq,new T(function(){return B(_I(0,_1hx,_10));}))):new T2(1,_1cp,new T2(1,_1jq,_10));}}};if(!E(_1hK)){return new F(function(){return _1jn(_);});}else{var _1jr=E(_1eH);if(E(_1jr.a)!=E(_1ji)){return new T2(1,_1cn,new T2(1,_1hz,_10));}else{if(E(_1jr.b)!=E(_1jh)){return new T2(1,_1cn,new T2(1,_1hz,_10));}else{return new F(function(){return _1jn(_);});}}}};if(!E(_1hK)){return B(_1jl(_));}else{if(!E(_1jj)){return B(_1jl(_));}else{return E(_1cg);}}}else{return new T2(1,_1ck,new T2(1,_1hz,_10));}}else{return new T2(1,_1cj,new T2(1,_1hz,_10));}},1);return {_:0,a:new T2(0,_1ji,_1jh),b:_1iq,c:_1jc,d:_1je,e:_1eL,f:_1eM,g:B(_y(_1eN,_1jk)),h:_1eO,i:E(_1jj)};};if(!E(_1hI)){return new F(function(){return _1jd(_1eK);});}else{return new F(function(){return _1jd(E(_1hz));});}};if(!E(_1hD)){var _1js=B(_1jb(_1eJ));return {_:0,a:E(_1js.a),b:E(_1js.b),c:_1js.c,d:_1js.d,e:_1js.e,f:_1js.f,g:E(_1js.g),h:E(_1js.h),i:E(_1js.i)};}else{var _1jt=B(_1jb(E(_1hz)));return {_:0,a:E(_1jt.a),b:E(_1jt.b),c:_1jt.c,d:_1jt.d,e:_1jt.e,f:_1jt.f,g:E(_1jt.g),h:E(_1jt.h),i:E(_1jt.i)};}};switch(E(_1fs)){case 72:var _1ju=E(_1eH),_1jv=_1ju.a,_1jw=E(_1ju.b);if(0<=(_1jw-1|0)){return B(_1fu(_1jv,_1jw-1|0));}else{return B(_1fu(_1jv,_1jw));}break;case 75:var _1jx=E(_1eH),_1jy=_1jx.b,_1jz=E(_1jx.a);if(0<=(_1jz-1|0)){return B(_1hu(_1jz-1|0,_1jy));}else{return B(_1hu(_1jz,_1jy));}break;case 77:var _1jA=E(_1eH),_1jB=_1jA.b,_1jC=E(_1jA.a);if(E(_1eQ)!=(_1jC+1|0)){return B(_1hu(_1jC+1|0,_1jB));}else{return B(_1hu(_1jC,_1jB));}break;case 80:var _1jD=E(_1eH),_1jE=_1jD.a,_1jF=E(_1jD.b);if(E(_1eR)!=(_1jF+1|0)){return B(_1fu(_1jE,_1jF+1|0));}else{return B(_1fu(_1jE,_1jF));}break;case 104:var _1jG=E(_1eH),_1jH=_1jG.b,_1jI=E(_1jG.a);if(0<=(_1jI-1|0)){return B(_1hu(_1jI-1|0,_1jH));}else{return B(_1hu(_1jI,_1jH));}break;case 106:var _1jJ=E(_1eH),_1jK=_1jJ.a,_1jL=E(_1jJ.b);if(E(_1eR)!=(_1jL+1|0)){return B(_1fu(_1jK,_1jL+1|0));}else{return B(_1fu(_1jK,_1jL));}break;case 107:var _1jM=E(_1eH),_1jN=_1jM.a,_1jO=E(_1jM.b);if(0<=(_1jO-1|0)){return B(_1fu(_1jN,_1jO-1|0));}else{return B(_1fu(_1jN,_1jO));}break;case 108:var _1jP=E(_1eH),_1jQ=_1jP.b,_1jR=E(_1jP.a);if(E(_1eQ)!=(_1jR+1|0)){return B(_1hu(_1jR+1|0,_1jQ));}else{return B(_1hu(_1jR,_1jQ));}break;default:var _1jS=E(_1eH),_1jT=E(_1jS.a),_1jU=E(_1jS.b),_1jV=B(_77(B(_77(_1eI,_1jU)),_1jT)),_1jW=_1jV.a,_1jX=_1jV.b;if(E(_1eK)==32){if(!B(_4B(_6f,_1jW,_18a))){var _1jY=false;}else{switch(E(_1jX)){case 0:var _1jZ=true;break;case 1:var _1jZ=false;break;case 2:var _1jZ=false;break;case 3:var _1jZ=false;break;case 4:var _1jZ=false;break;case 5:var _1jZ=false;break;case 6:var _1jZ=false;break;case 7:var _1jZ=false;break;default:var _1jZ=false;}var _1jY=_1jZ;}var _1k0=_1jY;}else{var _1k0=false;}if(E(_1eK)==32){if(E(_1jW)==32){var _1k1=false;}else{switch(E(_1jX)){case 0:if(!E(_1k0)){var _1k2=true;}else{var _1k2=false;}var _1k3=_1k2;break;case 1:var _1k3=false;break;case 2:var _1k3=false;break;case 3:var _1k3=false;break;case 4:var _1k3=false;break;case 5:var _1k3=false;break;case 6:var _1k3=false;break;case 7:var _1k3=false;break;default:if(!E(_1k0)){var _1k4=true;}else{var _1k4=false;}var _1k3=_1k4;}var _1k1=_1k3;}var _1k5=_1k1;}else{var _1k5=false;}var _1k6=new T(function(){return B(_m9(_1jT,_1jU,new T(function(){if(!E(_1k5)){if(!E(_1k0)){return E(_1jW);}else{return _1eJ;}}else{return E(_1ca);}}),_1jX,_1eI));});switch(E(_1jX)){case 3:var _1k7=true;break;case 4:if(E(_1eK)==32){var _1k8=true;}else{var _1k8=false;}var _1k7=_1k8;break;default:var _1k7=false;}if(!E(_1k7)){var _1k9=E(_1k6);}else{var _1k9=E(_1cs);}if(!E(_1eO)){var _1ka=E(_1k9);}else{var _1kb=new T(function(){var _1kc=E(_1k9);if(!_1kc._){return E(_dJ);}else{return B(_7a(_1kc.a,0));}}),_1kd=new T(function(){return B(_7a(_1k9,0));}),_1ke=function(_1kf,_1kg,_1kh,_1ki,_1kj,_1kk,_1kl){while(1){var _1km=B((function(_1kn,_1ko,_1kp,_1kq,_1kr,_1ks,_1kt){var _1ku=E(_1kt);if(!_1ku._){return E(_1kq);}else{var _1kv=_1ku.b,_1kw=E(_1ku.a);if(!_1kw._){return E(_1cr);}else{var _1kx=_1kw.b,_1ky=E(_1kw.a);if(E(_1ky.b)==5){var _1kz=new T(function(){var _1kA=B(_17I(_1eb,_1kn));return new T2(0,_1kA.a,_1kA.b);}),_1kB=new T(function(){var _1kC=function(_1kD,_1kE){var _1kF=function(_1kG){return new F(function(){return _m9(_1ko,_1kp,_1ca,_AQ,new T(function(){return B(_m9(_1kD,_1kE,_1ky.a,_13J,_1kq));}));});};if(_1kD!=_1ko){return new F(function(){return _1kF(_);});}else{if(_1kE!=_1kp){return new F(function(){return _1kF(_);});}else{return E(_1kq);}}};switch(E(E(_1kz).a)){case 1:var _1kH=_1ko-1|0;if(_1kH<0){return B(_1kC(_1ko,_1kp));}else{if(_1kH>=E(_1kb)){return B(_1kC(_1ko,_1kp));}else{if(_1kp<0){return B(_1kC(_1ko,_1kp));}else{if(_1kp>=E(_1kd)){return B(_1kC(_1ko,_1kp));}else{if(_1kH!=_1kr){if(E(B(_77(B(_77(_1kq,_1kp)),_1kH)).a)==32){return B(_1kC(_1kH,_1kp));}else{return B(_1kC(_1ko,_1kp));}}else{if(_1kp!=_1ks){if(E(B(_77(B(_77(_1kq,_1kp)),_1kH)).a)==32){return B(_1kC(_1kH,_1kp));}else{return B(_1kC(_1ko,_1kp));}}else{return B(_1kC(_1ko,_1kp));}}}}}}break;case 2:if(_1ko<0){return B(_1kC(_1ko,_1kp));}else{if(_1ko>=E(_1kb)){return B(_1kC(_1ko,_1kp));}else{var _1kI=_1kp-1|0;if(_1kI<0){return B(_1kC(_1ko,_1kp));}else{if(_1kI>=E(_1kd)){return B(_1kC(_1ko,_1kp));}else{if(_1ko!=_1kr){if(E(B(_77(B(_77(_1kq,_1kI)),_1ko)).a)==32){return B(_1kC(_1ko,_1kI));}else{return B(_1kC(_1ko,_1kp));}}else{if(_1kI!=_1ks){if(E(B(_77(B(_77(_1kq,_1kI)),_1ko)).a)==32){return B(_1kC(_1ko,_1kI));}else{return B(_1kC(_1ko,_1kp));}}else{return B(_1kC(_1ko,_1kp));}}}}}}break;case 3:var _1kJ=_1ko+1|0;if(_1kJ<0){return B(_1kC(_1ko,_1kp));}else{if(_1kJ>=E(_1kb)){return B(_1kC(_1ko,_1kp));}else{if(_1kp<0){return B(_1kC(_1ko,_1kp));}else{if(_1kp>=E(_1kd)){return B(_1kC(_1ko,_1kp));}else{if(_1kJ!=_1kr){if(E(B(_77(B(_77(_1kq,_1kp)),_1kJ)).a)==32){return B(_1kC(_1kJ,_1kp));}else{return B(_1kC(_1ko,_1kp));}}else{if(_1kp!=_1ks){if(E(B(_77(B(_77(_1kq,_1kp)),_1kJ)).a)==32){return B(_1kC(_1kJ,_1kp));}else{return B(_1kC(_1ko,_1kp));}}else{return B(_1kC(_1ko,_1kp));}}}}}}break;case 4:if(_1ko<0){return B(_1kC(_1ko,_1kp));}else{if(_1ko>=E(_1kb)){return B(_1kC(_1ko,_1kp));}else{var _1kK=_1kp+1|0;if(_1kK<0){return B(_1kC(_1ko,_1kp));}else{if(_1kK>=E(_1kd)){return B(_1kC(_1ko,_1kp));}else{if(_1ko!=_1kr){if(E(B(_77(B(_77(_1kq,_1kK)),_1ko)).a)==32){return B(_1kC(_1ko,_1kK));}else{return B(_1kC(_1ko,_1kp));}}else{if(_1kK!=_1ks){if(E(B(_77(B(_77(_1kq,_1kK)),_1ko)).a)==32){return B(_1kC(_1ko,_1kK));}else{return B(_1kC(_1ko,_1kp));}}else{return B(_1kC(_1ko,_1kp));}}}}}}break;default:if(_1ko<0){return B(_1kC(_1ko,_1kp));}else{if(_1ko>=E(_1kb)){return B(_1kC(_1ko,_1kp));}else{if(_1kp<0){return B(_1kC(_1ko,_1kp));}else{if(_1kp>=E(_1kd)){return B(_1kC(_1ko,_1kp));}else{if(_1ko!=_1kr){var _1kL=E(B(_77(B(_77(_1kq,_1kp)),_1ko)).a);return B(_1kC(_1ko,_1kp));}else{if(_1kp!=_1ks){var _1kM=E(B(_77(B(_77(_1kq,_1kp)),_1ko)).a);return B(_1kC(_1ko,_1kp));}else{return B(_1kC(_1ko,_1kp));}}}}}}}}),_1kN=E(_1kx);if(!_1kN._){var _1kO=_1kp+1|0,_1kP=_1kr,_1kQ=_1ks;_1kf=new T(function(){return E(E(_1kz).b);},1);_1kg=0;_1kh=_1kO;_1ki=_1kB;_1kj=_1kP;_1kk=_1kQ;_1kl=_1kv;return __continue;}else{return new F(function(){return _1kR(new T(function(){return E(E(_1kz).b);},1),_1ko+1|0,_1kp,_1kB,_1kr,_1ks,_1kN.a,_1kN.b,_1kv);});}}else{var _1kS=E(_1kx);if(!_1kS._){var _1kT=_1kn,_1kO=_1kp+1|0,_1kU=_1kq,_1kP=_1kr,_1kQ=_1ks;_1kf=_1kT;_1kg=0;_1kh=_1kO;_1ki=_1kU;_1kj=_1kP;_1kk=_1kQ;_1kl=_1kv;return __continue;}else{return new F(function(){return _1kR(_1kn,_1ko+1|0,_1kp,_1kq,_1kr,_1ks,_1kS.a,_1kS.b,_1kv);});}}}}})(_1kf,_1kg,_1kh,_1ki,_1kj,_1kk,_1kl));if(_1km!=__continue){return _1km;}}},_1kR=function(_1kV,_1kW,_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3){while(1){var _1l4=B((function(_1l5,_1l6,_1l7,_1l8,_1l9,_1la,_1lb,_1lc,_1ld){var _1le=E(_1lb);if(E(_1le.b)==5){var _1lf=new T(function(){var _1lg=B(_17I(_1eb,_1l5));return new T2(0,_1lg.a,_1lg.b);}),_1lh=new T(function(){var _1li=function(_1lj,_1lk){var _1ll=function(_1lm){return new F(function(){return _m9(_1l6,_1l7,_1ca,_AQ,new T(function(){return B(_m9(_1lj,_1lk,_1le.a,_13J,_1l8));}));});};if(_1lj!=_1l6){return new F(function(){return _1ll(_);});}else{if(_1lk!=_1l7){return new F(function(){return _1ll(_);});}else{return E(_1l8);}}};switch(E(E(_1lf).a)){case 1:var _1ln=_1l6-1|0;if(_1ln<0){return B(_1li(_1l6,_1l7));}else{if(_1ln>=E(_1kb)){return B(_1li(_1l6,_1l7));}else{if(_1l7<0){return B(_1li(_1l6,_1l7));}else{if(_1l7>=E(_1kd)){return B(_1li(_1l6,_1l7));}else{if(_1ln!=_1l9){if(E(B(_77(B(_77(_1l8,_1l7)),_1ln)).a)==32){return B(_1li(_1ln,_1l7));}else{return B(_1li(_1l6,_1l7));}}else{if(_1l7!=_1la){if(E(B(_77(B(_77(_1l8,_1l7)),_1ln)).a)==32){return B(_1li(_1ln,_1l7));}else{return B(_1li(_1l6,_1l7));}}else{return B(_1li(_1l6,_1l7));}}}}}}break;case 2:if(_1l6<0){return B(_1li(_1l6,_1l7));}else{if(_1l6>=E(_1kb)){return B(_1li(_1l6,_1l7));}else{var _1lo=_1l7-1|0;if(_1lo<0){return B(_1li(_1l6,_1l7));}else{if(_1lo>=E(_1kd)){return B(_1li(_1l6,_1l7));}else{if(_1l6!=_1l9){if(E(B(_77(B(_77(_1l8,_1lo)),_1l6)).a)==32){return B(_1li(_1l6,_1lo));}else{return B(_1li(_1l6,_1l7));}}else{if(_1lo!=_1la){if(E(B(_77(B(_77(_1l8,_1lo)),_1l6)).a)==32){return B(_1li(_1l6,_1lo));}else{return B(_1li(_1l6,_1l7));}}else{return B(_1li(_1l6,_1l7));}}}}}}break;case 3:var _1lp=_1l6+1|0;if(_1lp<0){return B(_1li(_1l6,_1l7));}else{if(_1lp>=E(_1kb)){return B(_1li(_1l6,_1l7));}else{if(_1l7<0){return B(_1li(_1l6,_1l7));}else{if(_1l7>=E(_1kd)){return B(_1li(_1l6,_1l7));}else{if(_1lp!=_1l9){if(E(B(_77(B(_77(_1l8,_1l7)),_1lp)).a)==32){return B(_1li(_1lp,_1l7));}else{return B(_1li(_1l6,_1l7));}}else{if(_1l7!=_1la){if(E(B(_77(B(_77(_1l8,_1l7)),_1lp)).a)==32){return B(_1li(_1lp,_1l7));}else{return B(_1li(_1l6,_1l7));}}else{return B(_1li(_1l6,_1l7));}}}}}}break;case 4:if(_1l6<0){return B(_1li(_1l6,_1l7));}else{if(_1l6>=E(_1kb)){return B(_1li(_1l6,_1l7));}else{var _1lq=_1l7+1|0;if(_1lq<0){return B(_1li(_1l6,_1l7));}else{if(_1lq>=E(_1kd)){return B(_1li(_1l6,_1l7));}else{if(_1l6!=_1l9){if(E(B(_77(B(_77(_1l8,_1lq)),_1l6)).a)==32){return B(_1li(_1l6,_1lq));}else{return B(_1li(_1l6,_1l7));}}else{if(_1lq!=_1la){if(E(B(_77(B(_77(_1l8,_1lq)),_1l6)).a)==32){return B(_1li(_1l6,_1lq));}else{return B(_1li(_1l6,_1l7));}}else{return B(_1li(_1l6,_1l7));}}}}}}break;default:if(_1l6<0){return B(_1li(_1l6,_1l7));}else{if(_1l6>=E(_1kb)){return B(_1li(_1l6,_1l7));}else{if(_1l7<0){return B(_1li(_1l6,_1l7));}else{if(_1l7>=E(_1kd)){return B(_1li(_1l6,_1l7));}else{if(_1l6!=_1l9){var _1lr=E(B(_77(B(_77(_1l8,_1l7)),_1l6)).a);return B(_1li(_1l6,_1l7));}else{if(_1l7!=_1la){var _1ls=E(B(_77(B(_77(_1l8,_1l7)),_1l6)).a);return B(_1li(_1l6,_1l7));}else{return B(_1li(_1l6,_1l7));}}}}}}}}),_1lt=E(_1lc);if(!_1lt._){return new F(function(){return _1ke(new T(function(){return E(E(_1lf).b);},1),0,_1l7+1|0,_1lh,_1l9,_1la,_1ld);});}else{var _1lu=_1l6+1|0,_1lv=_1l7,_1lw=_1l9,_1lx=_1la,_1ly=_1ld;_1kV=new T(function(){return E(E(_1lf).b);},1);_1kW=_1lu;_1kX=_1lv;_1kY=_1lh;_1kZ=_1lw;_1l0=_1lx;_1l1=_1lt.a;_1l2=_1lt.b;_1l3=_1ly;return __continue;}}else{var _1lz=E(_1lc);if(!_1lz._){return new F(function(){return _1ke(_1l5,0,_1l7+1|0,_1l8,_1l9,_1la,_1ld);});}else{var _1lA=_1l5,_1lu=_1l6+1|0,_1lv=_1l7,_1lB=_1l8,_1lw=_1l9,_1lx=_1la,_1ly=_1ld;_1kV=_1lA;_1kW=_1lu;_1kX=_1lv;_1kY=_1lB;_1kZ=_1lw;_1l0=_1lx;_1l1=_1lz.a;_1l2=_1lz.b;_1l3=_1ly;return __continue;}}})(_1kV,_1kW,_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3));if(_1l4!=__continue){return _1l4;}}},_1ka=B(_1ke(_1eM,0,0,_1k9,_1jT,_1jU,_1k9));}var _1lC=function(_1lD){var _1lE=function(_1lF){var _1lG=new T(function(){switch(E(_1jX)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1lH=new T(function(){if(!E(_1k7)){if(!E(_1lG)){return new T2(0,_1jT,_1jU);}else{return E(_1jS);}}else{if(!B(_6E(_6Q,_1ka,_1k6))){if(!E(_1lG)){return new T2(0,_1jT,_1jU);}else{return E(_1jS);}}else{return E(_1jS);}}}),_1lI=new T(function(){return E(E(_1lH).b);}),_1lJ=new T(function(){return E(E(_1lH).a);});if(!E(_1k7)){var _1lK=E(_1eP);}else{var _1lK=E(B(_SK(new T(function(){return B(_19D(_1eL,_1bV,_1ka));}),_1ka)).a);}var _1lL=new T(function(){if(!E(_1k5)){if(!E(_1k0)){var _1lM=function(_1lN){var _1lO=function(_1lP){var _1lQ=E(_1jX);if(_1lQ==4){return new T2(1,_1co,new T2(1,_1jW,_10));}else{if(!E(_1lG)){return (E(_1lQ)==2)?new T2(1,_1cq,new T2(1,_1jW,_10)):__Z;}else{var _1lR=E(_1jW);return (E(_1lR)==61)?new T2(1,_1cp,new T2(1,_1lR,new T(function(){return B(_I(0,_1jU,_10));}))):new T2(1,_1cp,new T2(1,_1lR,_10));}}};if(!E(_1k7)){return new F(function(){return _1lO(_);});}else{if(_1jT!=E(_1lJ)){return new T2(1,_1cn,new T2(1,_1jW,_10));}else{if(_1jU!=E(_1lI)){return new T2(1,_1cn,new T2(1,_1jW,_10));}else{return new F(function(){return _1lO(_);});}}}};if(!E(_1k7)){return B(_1lM(_));}else{if(!E(_1lK)){return B(_1lM(_));}else{return E(_1cg);}}}else{return new T2(1,_1ck,new T2(1,_1jW,_10));}}else{return new T2(1,_1cj,new T2(1,_1jW,_10));}},1);return {_:0,a:new T2(0,_1lJ,_1lI),b:_1ka,c:_1lD,d:_1lF,e:_1eL,f:_1eM,g:B(_y(_1eN,_1lL)),h:_1eO,i:E(_1lK)};};if(!E(_1k5)){return new F(function(){return _1lE(_1eK);});}else{return new F(function(){return _1lE(E(_1jW));});}};if(!E(_1k0)){var _1lS=B(_1lC(_1eJ));return {_:0,a:E(_1lS.a),b:E(_1lS.b),c:_1lS.c,d:_1lS.d,e:_1lS.e,f:_1lS.f,g:E(_1lS.g),h:E(_1lS.h),i:E(_1lS.i)};}else{var _1lT=B(_1lC(E(_1jW)));return {_:0,a:E(_1lT.a),b:E(_1lT.b),c:_1lT.c,d:_1lT.d,e:_1lT.e,f:_1lT.f,g:E(_1lT.g),h:E(_1lT.h),i:E(_1lT.i)};}}}),_1lU=new T(function(){if(E(_1fs)==32){var _1lV=E(_1ft),_1lW=_1lV.b,_1lX=_1lV.c,_1lY=_1lV.d,_1lZ=_1lV.e,_1m0=_1lV.f,_1m1=_1lV.g,_1m2=_1lV.h,_1m3=E(_1lV.a),_1m4=_1m3.a,_1m5=E(_1m3.b),_1m6=new T(function(){return B(_77(B(_77(_1lW,_1m5)),E(_1m4)));}),_1m7=new T(function(){return E(E(_1m6).b);}),_1m8=new T(function(){if(E(_1m7)==4){return true;}else{return false;}}),_1m9=new T(function(){return E(E(_1m6).a);});if(E(_1lY)==32){var _1ma=false;}else{if(E(_1m9)==32){var _1mb=true;}else{var _1mb=false;}var _1ma=_1mb;}var _1mc=new T(function(){var _1md=new T(function(){return B(A3(_77,_188,B(_iC(_6f,_1lX,_18a)),_1lY));});if(!E(_1ma)){if(!E(_1m8)){return E(_1m9);}else{if(!B(_4B(_3M,_1lZ,_18E))){return E(_1m9);}else{return B(A(_77,[_18C,B(_iC(_3M,_1lZ,_18E)),_1md,_1m9]));}}}else{return E(_1md);}}),_1me=B(_m9(_1m4,_1m5,_1mc,_1m7,_1lW));if(!E(_1ma)){var _1mf=B(_SK(new T(function(){return B(_19D(_1lZ,_1bV,_1me));}),_1me)).a;return {_:0,a:E(_1m3),b:E(_1me),c:_1lX,d:_1lY,e:_1lZ,f:_1m0,g:E(B(_y(_1m1,new T(function(){if(!E(_1mf)){if(!E(_1m8)){return __Z;}else{return new T2(1,_1ci,new T2(1,_1mc,_10));}}else{return E(_1cg);}},1)))),h:E(_1m2),i:E(_1mf)};}else{var _1mg=B(_SK(new T(function(){return B(_19D(_1lZ,_1bV,_1me));}),_1me)).a;return {_:0,a:E(_1m3),b:E(_1me),c:_1lX,d:32,e:_1lZ,f:_1m0,g:E(B(_y(_1m1,new T(function(){if(!E(_1mg)){return new T2(1,_1ch,new T2(1,_1mc,_10));}else{return E(_1cg);}},1)))),h:E(_1m2),i:E(_1mg)};}}else{return E(_1ft);}}),_1mh=new T(function(){var _1mi=E(_1lU),_1mj=_1mi.g,_1mk=B(_15n(_1bW,_1mj,_1eT,{_:0,a:E(_1mi.a),b:E(_1mi.b),c:_1mi.c,d:_1mi.d,e:_1mi.e,f:E(E(_1fo).b),g:E(_1mj),h:E(_1mi.h),i:E(_1mi.i)},_1fe,_1eS,_1eT,_1eU,_1eV,_1fd,_1eY,_1eZ,_1f0,_1f1,_1f2,_1f3,_1f4,_1f5,_1f6,_qO,_1f8,_qO,_1fa,_1fb,_1fc));return {_:0,a:E(_1mk.a),b:E(_1mk.b),c:E(_1mk.c),d:E(_1mk.d),e:E(_1mk.e),f:E(_1mk.f),g:E(_1mk.g),h:_1mk.h,i:_1mk.i,j:_1mk.j,k:_1mk.k,l:E(_1mk.l),m:_1mk.m,n:E(_1mk.n),o:E(_1mk.o),p:E(_1mk.p),q:E(_1mk.q),r:E(_1mk.r),s:E(_1mk.s),t:E(_1mk.t),u:E(_1mk.u),v:_1mk.v};}),_1ml=B(_dT(_1fq,_1fr,new T(function(){return 26-E(E(E(_1mh).b).a)|0;}),_ep,new T(function(){return E(E(E(_1mh).a).b);}),_)),_1mm=E(_1mh),_1mn=_1mm.c,_1mo=_1mm.d,_1mp=_1mm.e,_1mq=_1mm.f,_1mr=_1mm.h,_1ms=_1mm.i,_1mt=_1mm.j,_1mu=_1mm.k,_1mv=_1mm.l,_1mw=_1mm.m,_1mx=_1mm.n,_1my=_1mm.q,_1mz=_1mm.r,_1mA=_1mm.s,_1mB=_1mm.t,_1mC=_1mm.u,_1mD=_1mm.v,_1mE=E(_1mm.a),_1mF=_1mE.e,_1mG=_1mE.f,_1mH=E(_1mm.g),_1mI=function(_){var _1mJ=function(_1mK){var _1mL=function(_1mM){if(_1mM!=E(_1ce)){var _1mN=B(_77(_Yq,_1mM)),_1mO=_1mN.a,_1mP=E(_1mN.b),_1mQ=B(_UZ(_1mO,_1mP,new T(function(){return B(_77(_13E,_1mM));})));return new F(function(){return _1eE(_1fp,_1cd,B(_77(_YA,_1mM)),_1mQ,B(_77(_YD,_1mM)),32,_1mM,_1mG,B(_y(_1mE.g,new T2(1,_1cc,new T(function(){return B(_I(0,_1mF,_10));})))),B(_1al(_1cb,_1mQ)),_qO,_1mO,_1mP,_10,_1mo,_1mp,_1mq,_1mH.a,_1mH.b,_1mr,_1ms,_1mt, -1,_1mv,_1mw,_qO,_qO,_qO,_1my,_1mz,_1mA,_1mB,_1mC,_1mD,_);});}else{var _1mR=__app1(E(_dK),_1fr),_1mS=B(A2(_dM,_1fq,_)),_1mT=B(A(_dg,[_1fq,_dL,_1e8,_1eb,_1c9,_])),_1mU=B(A(_dg,[_1fq,_dL,_1c6,_1c8,_1c7,_])),_1mV=B(A(_dg,[_1fq,_dL,_1c6,_1c5,_1c4,_])),_1mW=B(A(_dg,[_1fq,_dL,_1c3,_1c2,_1c1,_])),_1mX=B(A(_dg,[_1fq,_dL,_1eb,_1ea,_1e9,_])),_1mY=B(A(_dg,[_1fq,_dL,_1e8,_1e7,_1ct,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_Yz),b:E(_1bX),c:E(_1cl),d:32,e:0,f:_1mG,g:E(_10),h:E(_1mE.h),i:E(_qO)}),b:E(_Yp),c:E(_1mn),d:E(_1mo),e:E(_1mp),f:E(_1mq),g:E(_1mH),h:_1mr,i:_1ms,j:_1mt,k:_1mu,l:E(_1mv),m:_1mw,n:E(_1mx),o:E(_qO),p:E(_qO),q:E(_1my),r:E(_1mz),s:E(_1mA),t:E(_1mB),u:E(_1mC),v:_1mD};});}};if(_1mu>=0){return new F(function(){return _1mL(_1mu);});}else{return new F(function(){return _1mL(_1mF+1|0);});}};if(!E(_1mx)){if(E(_1fs)==110){return new F(function(){return _1mJ(_);});}else{var _1mZ=new T(function(){return E(E(_1ft).a);});if(E(_1mE.d)==32){var _1n0=B(A(_dg,[_1fq,_1bY,new T(function(){return ((E(E(_1mZ).a)+1|0)+26|0)-E(_1eQ)|0;},1),new T(function(){return (E(E(_1mZ).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_eq(_1lU));}),_10),_]));return _1mm;}else{var _1n1=B(A(_dg,[_1fq,_1cf,new T(function(){return ((E(E(_1mZ).a)+1|0)+26|0)-E(_1eQ)|0;},1),new T(function(){return (E(E(_1mZ).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_eq(_1lU));}),_10),_]));return _1mm;}}}else{return new F(function(){return _1mJ(_);});}};if(!E(_1mm.p)){var _1n2=new T(function(){return (2+E(_1eR)|0)+3|0;}),_1n3=B(_Ev(_1fp,_Ec,_1n2,15+_1mt|0,_1n2,_1mn,_));return new F(function(){return _1mI(_);});}else{return new F(function(){return _1mI(_);});}};if(!E(_1fa)){var _1n4=B(_1aP(_1eD,_1eB,_));return new F(function(){return _1fn(_);});}else{var _1n5=B(_1aP(_1eD,_1eA,_));return new F(function(){return _1fn(_);});}};if(!E(_1eP)){var _1n6=B(_1aP(_1eD,_1eB,_));return new F(function(){return _1fm(_);});}else{var _1n7=B(_1aP(_1eD,_1eA,_));return new F(function(){return _1fm(_);});}},_1n8=E(_1eV);if(!_1n8._){var _1n9=B(_1aP(_1eD,_1e5,_));return new F(function(){return _1fk(_);});}else{var _1na=new T(function(){var _1nb=E(_1n8.a),_1nc=new T(function(){return B(A3(_1aE,_6R,new T2(1,function(_1nd){return new F(function(){return _1ed(_1nb.a,_1nd);});},new T2(1,function(_1ne){return new F(function(){return _1ed(_1nb.b,_1ne);});},_10)),new T2(1,_G,new T(function(){return B(_1eg(_1n8.b));}))));});return new T2(1,_H,_1nc);}),_1nf=B(_1aP(_1eD,new T2(1,_2C,_1na),_));return new F(function(){return _1fk(_);});}},_1ng=E(_1eU);if(!_1ng._){var _1nh=B(_1aP(_1eD,_1e5,_));return new F(function(){return _1fj(_);});}else{var _1ni=new T(function(){return B(_I(0,E(_1ng.a),new T(function(){return B(_1eo(_1ng.b));})));}),_1nj=B(_1aP(_1eD,new T2(1,_2C,_1ni),_));return new F(function(){return _1fj(_);});}},_1nk=E(_1eT);if(!_1nk._){var _1nl=B(_1aP(_1eD,_1e5,_));return new F(function(){return _1fi(_);});}else{var _1nm=new T(function(){var _1nn=E(_1nk.a),_1no=new T(function(){return B(A3(_1aE,_6R,new T2(1,function(_1np){return new F(function(){return _1ed(_1nn.a,_1np);});},new T2(1,function(_1nq){return new F(function(){return _1ed(_1nn.b,_1nq);});},_10)),new T2(1,_G,new T(function(){return B(_1es(_1nk.b));}))));});return new T2(1,_H,_1no);}),_1nr=B(_1aP(_1eD,new T2(1,_2C,_1nm),_));return new F(function(){return _1fi(_);});}}else{if(!E(_1fa)){return {_:0,a:E(_1ff),b:E(_1fe),c:E(_1eS),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1f3,n:E(_1f4),o:E(_1f5),p:E(_1f6),q:E(_qO),r:E(_1f8),s:E(_qO),t:E(_qO),u:E(_1fb),v:_1fc};}else{var _1ns=B(_1aP(_1eD,_1e4,_)),_1nt=new T(function(){var _1nu=B(_17N(_1f2));return new T2(0,_1nu.a,_1nu.b);}),_1nv=new T(function(){return E(E(_1nt).a);}),_1nw=function(_1nx,_1ny){var _1nz=E(_1nx);switch(_1nz){case  -2:return {_:0,a:E(_1ff),b:E(_1fe),c:E(_1eS),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1f3,n:E(_1f4),o:E(_1f5),p:E(_1f6),q:E(_kr),r:E(_1f8),s:E(_qO),t:E(_kr),u:E(_1fb),v:_1fc};case  -1:var _1nA=E(_1eF),_1nB=B(_es(_1nA.a,_1nA.b,{_:0,a:E(_1ff),b:E(_1fe),c:E(_1eS),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1f3,n:E(_1f4),o:E(_1f5),p:E(_1f6),q:E(_kr),r:E(_1f8),s:E(_qO),t:E(_kr),u:E(_1fb),v:_1fc},_));return new T(function(){return {_:0,a:E(_1ff),b:E(_1fe),c:E(B(_Ye(new T(function(){return B(_77(E(_1nt).b,_1f3));})))),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1f3,n:E(_1f4),o:E(_1f5),p:E(_kr),q:E(_qO),r:E(_1f8),s:E(_qO),t:E(_qO),u:E(_1fb),v:_1fc};});default:var _1nC=E(_1eF),_1nD=B(_es(_1nC.a,_1nC.b,{_:0,a:E(_1ff),b:E(_1fe),c:E(_1eS),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1f3,n:E(_1f4),o:E(_1f5),p:E(_1f6),q:E(_kr),r:E(_1f8),s:E(_qO),t:E(_kr),u:E(_1fb),v:_1fc},_)),_1nE=new T(function(){return (2+E(_1eR)|0)+3|0;}),_1nF=B(_Ev(_1nC,_Ec,_1nE,15+_1f0|0,_1nE,B(_E4(_1eS,_1nv,_1ny)),_));return {_:0,a:E(_1ff),b:E(_1fe),c:E(_1eS),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1nz,n:E(_1f4),o:E(_1f5),p:E(_1f6),q:E(_kr),r:E(_1f8),s:E(_qO),t:E(_kr),u:E(_1fb),v:_1fc};}};switch(E(B(_17T(E(_1eG))))){case 32:return new F(function(){return _1nw( -1,_1bZ);});break;case 72:var _1nG=E(_1f3);if(!_1nG){var _1nH=B(_7a(_1nv,0))-1|0;return new F(function(){return _1nw(_1nH,_1nH);});}else{var _1nI=_1nG-1|0;return new F(function(){return _1nw(_1nI,_1nI);});}break;case 75:if(_1f3!=(B(_7a(_1nv,0))-1|0)){var _1nJ=_1f3+1|0;return new F(function(){return _1nw(_1nJ,_1nJ);});}else{return new F(function(){return _1nw(0,_1bW);});}break;case 77:var _1nK=E(_1f3);if(!_1nK){var _1nL=B(_7a(_1nv,0))-1|0;return new F(function(){return _1nw(_1nL,_1nL);});}else{var _1nM=_1nK-1|0;return new F(function(){return _1nw(_1nM,_1nM);});}break;case 80:if(_1f3!=(B(_7a(_1nv,0))-1|0)){var _1nN=_1f3+1|0;return new F(function(){return _1nw(_1nN,_1nN);});}else{return new F(function(){return _1nw(0,_1bW);});}break;case 104:if(_1f3!=(B(_7a(_1nv,0))-1|0)){var _1nO=_1f3+1|0;return new F(function(){return _1nw(_1nO,_1nO);});}else{return new F(function(){return _1nw(0,_1bW);});}break;case 106:if(_1f3!=(B(_7a(_1nv,0))-1|0)){var _1nP=_1f3+1|0;return new F(function(){return _1nw(_1nP,_1nP);});}else{return new F(function(){return _1nw(0,_1bW);});}break;case 107:var _1nQ=E(_1f3);if(!_1nQ){var _1nR=B(_7a(_1nv,0))-1|0;return new F(function(){return _1nw(_1nR,_1nR);});}else{var _1nS=_1nQ-1|0;return new F(function(){return _1nw(_1nS,_1nS);});}break;case 108:var _1nT=E(_1f3);if(!_1nT){var _1nU=B(_7a(_1nv,0))-1|0;return new F(function(){return _1nw(_1nU,_1nU);});}else{var _1nV=_1nT-1|0;return new F(function(){return _1nw(_1nV,_1nV);});}break;default:return new F(function(){return _1nw( -2,_1c0);});}}}};if(!E(_1f6)){return new F(function(){return _1fg(_);});}else{if(!E(_1f7)){return new F(function(){return _J1(_1eF,_1eH,_1eI,_1eJ,_1eK,_1eL,_1eM,_1eN,_1eO,_1eP,_1eQ,_1eR,_1eS,_1eT,_1eU,_1eV,_1eW,_1eX,_1eY,_1eZ,_1f0,_1f1,_1f2,_1f3,_1f4,_1f5,_qO,_1f8,_kr,_1fa,_1fb,_1fc,_);});}else{return new F(function(){return _1fg(_);});}}}else{return {_:0,a:E(_1ff),b:E(_1fe),c:E(_1eS),d:E(_1eT),e:E(_1eU),f:E(_1eV),g:E(_1fd),h:_1eY,i:_1eZ,j:_1f0,k:_1f1,l:E(_1f2),m:_1f3,n:E(_1f4),o:E(_1f5),p:E(_1f6),q:E(_1f7),r:E(_1f8),s:E(_kr),t:E(_1fa),u:E(_1fb),v:_1fc};}},_1nW=0,_1nX=2,_1nY=2,_1nZ=0,_1o0=new T(function(){return eval("document");}),_1o1=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1o2=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1o3=function(_1o4){return E(E(_1o4).b);},_1o5=function(_1o6,_1o7){return new F(function(){return A2(_1o3,_1o6,function(_){var _1o8=E(_1o7),_1o9=__app1(E(_1o2),_1o8);if(!_1o9){return _0;}else{var _1oa=__app1(E(_1o1),_1o8);return new T1(1,new T2(0,_1oa,_1o8));}});});},_1ob=new T2(0,_1bW,_1bW),_1oc=new T(function(){var _1od=E(_YD);if(!_1od._){return E(_dJ);}else{return {_:0,a:E({_:0,a:E(_Yz),b:E(_1bX),c:E(_1od.a),d:32,e:0,f:0,g:E(_10),h:E(_qO),i:E(_qO)}),b:E(_Yp),c:E(_Vy),d:E(_10),e:E(_10),f:E(_10),g:E(_1ob),h:0,i:0,j:0,k: -1,l:E(_10),m:0,n:E(_qO),o:E(_qO),p:E(_kr),q:E(_qO),r:E(_qO),s:E(_qO),t:E(_qO),u:E(_10),v:32};}}),_1oe=new T(function(){return E(E(E(_1oc).a).b);}),_1of=new T(function(){return E(E(E(_1oc).b).a);}),_1og=new T(function(){return 26-E(_1of)|0;}),_1oh=new T(function(){return B(unCStr("@"));}),_1oi=new T(function(){return E(E(E(_1oc).a).a);}),_1oj=new T(function(){return (E(E(_1oi).b)+2|0)+1|0;}),_1ok=new T(function(){return ((E(E(_1oi).a)+1|0)+26|0)-E(_1of)|0;}),_1ol=new T1(0,100),_1om=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/teru/Documents/haskell/haste/fi/Main.hs:12:3-9"));}),_1on=new T6(0,_0,_2V,_10,_1om,_0,_0),_1oo=new T(function(){return B(_2T(_1on));}),_1op=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/teru/Documents/haskell/haste/fi/Main.hs:13:3-8"));}),_1oq=new T6(0,_0,_2V,_10,_1op,_0,_0),_1or=new T(function(){return B(_2T(_1oq));}),_1os=new T1(1,50),_1ot=function(_1ou,_1ov,_1ow){var _1ox=E(_1ow);if(!_1ox._){return 0;}else{var _1oy=_1ox.b,_1oz=E(_1ox.a),_1oA=_1oz.a,_1oB=_1oz.b;return (_1ou<=_1oA)?1+B(_1ot(_1ou,_1ov,_1oy))|0:(_1ou>=_1oA+_1oz.c)?1+B(_1ot(_1ou,_1ov,_1oy))|0:(_1ov<=_1oB)?1+B(_1ot(_1ou,_1ov,_1oy))|0:(_1ov>=_1oB+_1oz.d)?1+B(_1ot(_1ou,_1ov,_1oy))|0:1;}},_1oC=function(_1oD,_1oE,_1oF){var _1oG=E(_1oF);if(!_1oG._){return 0;}else{var _1oH=_1oG.b,_1oI=E(_1oG.a),_1oJ=_1oI.a,_1oK=_1oI.b;if(_1oD<=_1oJ){return 1+B(_1oC(_1oD,_1oE,_1oH))|0;}else{if(_1oD>=_1oJ+_1oI.c){return 1+B(_1oC(_1oD,_1oE,_1oH))|0;}else{var _1oL=E(_1oE);return (_1oL<=_1oK)?1+B(_1ot(_1oD,_1oL,_1oH))|0:(_1oL>=_1oK+_1oI.d)?1+B(_1ot(_1oD,_1oL,_1oH))|0:1;}}}},_1oM=function(_1oN,_1oO,_1oP){var _1oQ=E(_1oP);if(!_1oQ._){return 0;}else{var _1oR=_1oQ.b,_1oS=E(_1oQ.a),_1oT=_1oS.a,_1oU=_1oS.b,_1oV=E(_1oN);if(_1oV<=_1oT){return 1+B(_1oC(_1oV,_1oO,_1oR))|0;}else{if(_1oV>=_1oT+_1oS.c){return 1+B(_1oC(_1oV,_1oO,_1oR))|0;}else{var _1oW=E(_1oO);return (_1oW<=_1oU)?1+B(_1ot(_1oV,_1oW,_1oR))|0:(_1oW>=_1oU+_1oS.d)?1+B(_1ot(_1oV,_1oW,_1oR))|0:1;}}}},_1oX=new T4(0,100,100,256,367),_1oY=new T2(1,_1oX,_10),_1oZ=new T4(0,356,100,100,467),_1p0=new T2(1,_1oZ,_1oY),_1p1=new T4(0,0,0,456,100),_1p2=new T2(1,_1p1,_1p0),_1p3=new T4(0,0,467,456,100),_1p4=new T2(1,_1p3,_1p2),_1p5=new T4(0,0,100,100,467),_1p6=new T2(1,_1p5,_1p4),_1p7=32,_1p8=76,_1p9=75,_1pa=74,_1pb=72,_1pc=64,_1pd=function(_1pe,_1pf,_1pg){var _1ph=new T(function(){switch(B(_1oM(_1pf,_1pg,_1p6))){case 1:return E(_1pb);break;case 2:return E(_1pa);break;case 3:return E(_1p9);break;case 4:return E(_1p8);break;case 5:return E(_1p7);break;default:return E(_1pc);}});return function(_1pi,_){var _1pj=E(_1pi),_1pk=E(_1pj.a),_1pl=E(_1pj.b),_1pm=E(_1pj.g);return new F(function(){return _1eE(_1pe,_1ph,_1pk.a,_1pk.b,_1pk.c,_1pk.d,_1pk.e,_1pk.f,_1pk.g,_1pk.h,_1pk.i,_1pl.a,_1pl.b,_1pj.c,_1pj.d,_1pj.e,_1pj.f,_1pm.a,_1pm.b,_1pj.h,_1pj.i,_1pj.j,_1pj.k,_1pj.l,_1pj.m,_1pj.n,_1pj.o,_1pj.p,_1pj.q,_1pj.r,_1pj.s,_1pj.t,_1pj.u,_1pj.v,_);});};},_1pn=function(_1po){return E(E(_1po).a);},_1pp=function(_1pq){return E(E(_1pq).a);},_1pr=function(_1ps){return E(E(_1ps).b);},_1pt=function(_1pu){return E(E(_1pu).b);},_1pv=function(_1pw){return E(E(_1pw).a);},_1px=function(_){return new F(function(){return nMV(_0);});},_1py=new T(function(){return B(_3(_1px));}),_1pz=function(_1pA){return E(E(_1pA).b);},_1pB=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1pC=function(_1pD){return E(E(_1pD).d);},_1pE=function(_1pF,_1pG,_1pH,_1pI,_1pJ,_1pK){var _1pL=B(_1pn(_1pF)),_1pM=B(_1pp(_1pL)),_1pN=new T(function(){return B(_1o3(_1pL));}),_1pO=new T(function(){return B(_1pC(_1pM));}),_1pP=new T(function(){return B(A1(_1pG,_1pI));}),_1pQ=new T(function(){return B(A2(_1pv,_1pH,_1pJ));}),_1pR=function(_1pS){return new F(function(){return A1(_1pO,new T3(0,_1pQ,_1pP,_1pS));});},_1pT=function(_1pU){var _1pV=new T(function(){var _1pW=new T(function(){var _1pX=__createJSFunc(2,function(_1pY,_){var _1pZ=B(A2(E(_1pU),_1pY,_));return _7;}),_1q0=_1pX;return function(_){return new F(function(){return __app3(E(_1pB),E(_1pP),E(_1pQ),_1q0);});};});return B(A1(_1pN,_1pW));});return new F(function(){return A3(_1pr,_1pM,_1pV,_1pR);});},_1q1=new T(function(){var _1q2=new T(function(){return B(_1o3(_1pL));}),_1q3=function(_1q4){var _1q5=new T(function(){return B(A1(_1q2,function(_){var _=wMV(E(_1py),new T1(1,_1q4));return new F(function(){return A(_1pt,[_1pH,_1pJ,_1q4,_]);});}));});return new F(function(){return A3(_1pr,_1pM,_1q5,_1pK);});};return B(A2(_1pz,_1pF,_1q3));});return new F(function(){return A3(_1pr,_1pM,_1q1,_1pT);});},_1q6=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1q7=function(_){var _1q8=rMV(E(_1py)),_1q9=E(_1q8);if(!_1q9._){var _1qa=__app1(E(_1q6),E(_7));return new F(function(){return _7g(_);});}else{var _1qb=__app1(E(_1q6),E(_1q9.a));return new F(function(){return _7g(_);});}},_1qc=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1qd=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1qe=function(_1qf,_1qg,_1qh){var _1qi=B(_1pn(_1qf)),_1qj=new T(function(){return B(_1o3(_1qi));}),_1qk=function(_1ql){var _1qm=function(_){var _1qn=E(_1qg);if(!_1qn._){var _1qo=B(A1(_1ql,_7f)),_1qp=__createJSFunc(0,function(_){var _1qq=B(A1(_1qo,_));return _7;}),_1qr=__app2(E(_1qd),_1qn.a,_1qp);return new T(function(){var _1qs=Number(_1qr),_1qt=jsTrunc(_1qs);return new T2(0,_1qt,E(_1qn));});}else{var _1qu=B(A1(_1ql,_7f)),_1qv=__createJSFunc(0,function(_){var _1qw=B(A1(_1qu,_));return _7;}),_1qx=__app2(E(_1qc),_1qn.a,_1qv);return new T(function(){var _1qy=Number(_1qx),_1qz=jsTrunc(_1qy);return new T2(0,_1qz,E(_1qn));});}};return new F(function(){return A1(_1qj,_1qm);});},_1qA=new T(function(){return B(A2(_1pz,_1qf,function(_1qB){return E(_1qh);}));});return new F(function(){return A3(_1pr,B(_1pp(_1qi)),_1qA,_1qk);});},_1qC=function(_,_1qD){var _1qE=E(_1qD);if(!_1qE._){return new F(function(){return die(_1oo);});}else{var _1qF=_1qE.a,_1qG=B(A3(_1o5,_5X,_1qF,_)),_1qH=E(_1qG);if(!_1qH._){return new F(function(){return die(_1or);});}else{var _1qI=E(_1qH.a),_1qJ=_1qI.a,_1qK=_1qI.b,_1qL=B(_dT(_1qJ,_1qK,_1og,_ep,_1oe,_)),_1qM=B(A(_dg,[_1qJ,_1bY,_1ok,_1oj,_1oh,_])),_1qN=nMV(_1oc),_1qO=_1qN,_1qP=B(A(_1pE,[_5Y,_3E,_u,_1o0,_1nX,function(_1qQ,_){var _1qR=B(_1q7(_)),_1qS=rMV(_1qO),_1qT=E(_1qS),_1qU=E(_1qT.a),_1qV=E(_1qT.b),_1qW=E(_1qT.g),_1qX=B(_1eE(_1qI,E(_1qQ).a,_1qU.a,_1qU.b,_1qU.c,_1qU.d,_1qU.e,_1qU.f,_1qU.g,_1qU.h,_1qU.i,_1qV.a,_1qV.b,_1qT.c,_1qT.d,_1qT.e,_1qT.f,_1qW.a,_1qW.b,_1qT.h,_1qT.i,_1qT.j,_1qT.k,_1qT.l,_1qT.m,_1qT.n,_1qT.o,_1qT.p,_1qT.q,_1qT.r,_1qT.s,_1qT.t,_1qT.u,_1qT.v,_)),_=wMV(_1qO,_1qX);return _7f;},_])),_1qY=function(_1qZ,_){var _1r0=E(E(_1qZ).a),_1r1=B(_63(_1qK,_)),_1r2=E(_1r1),_1r3=rMV(_1qO),_1r4=B(A(_1pd,[_1qI,new T(function(){return E(_1r0.a)*E(_1r2.a);},1),new T(function(){return E(_1r0.b)*E(_1r2.b);},1),_1r3,_])),_=wMV(_1qO,_1r4);return _7f;},_1r5=B(A(_1pE,[_5Y,_3E,_3D,_1qF,_1nW,_1qY,_])),_1r6=B(A(_1pE,[_5Y,_3E,_5d,_1qF,_1nZ,function(_1r7,_){var _1r8=E(_1r7),_1r9=rMV(_1qO),_1ra=E(_1r9);if(!E(_1ra.r)){var _=wMV(_1qO,_1ra);return _7f;}else{var _1rb=B(_1q7(_)),_=wMV(_1qO,_1ra);return _7f;}},_])),_1rc=function(_){var _1rd=rMV(_1qO),_=wMV(_1qO,new T(function(){var _1re=E(_1rd);return {_:0,a:E(_1re.a),b:E(_1re.b),c:E(_1re.c),d:E(_1re.d),e:E(_1re.e),f:E(_1re.f),g:E(_1re.g),h:_1re.h,i:_1re.i,j:_1re.j,k:_1re.k,l:E(_1re.l),m:_1re.m,n:E(_1re.n),o:E(_1re.o),p:E(_1re.p),q:E(_1re.q),r:E(_qO),s:E(_1re.s),t:E(_1re.t),u:E(_1re.u),v:_1re.v};}));return _7f;},_1rf=function(_1rg,_){var _1rh=E(_1rg),_1ri=rMV(_1qO),_=wMV(_1qO,new T(function(){var _1rj=E(_1ri);return {_:0,a:E(_1rj.a),b:E(_1rj.b),c:E(_1rj.c),d:E(_1rj.d),e:E(_1rj.e),f:E(_1rj.f),g:E(_1rj.g),h:_1rj.h,i:_1rj.i,j:_1rj.j,k:_1rj.k,l:E(_1rj.l),m:_1rj.m,n:E(_1rj.n),o:E(_1rj.o),p:E(_1rj.p),q:E(_1rj.q),r:E(_kr),s:E(_1rj.s),t:E(_1rj.t),u:E(_1rj.u),v:_1rj.v};})),_1rk=B(A(_1qe,[_5Y,_1ol,_1rc,_]));return _7f;},_1rl=B(A(_1pE,[_5Y,_3E,_5d,_1qF,_1nY,_1rf,_])),_1rm=B(A(_1qe,[_5Y,_1os,function(_){var _1rn=rMV(_1qO),_1ro=E(_1rn),_1rp=E(_1ro.a),_1rq=E(_1ro.b),_1rr=E(_1ro.g),_1rs=B(_Gm(_1qI,_1rp.a,_1rp.b,_1rp.c,_1rp.d,_1rp.e,_1rp.f,_1rp.g,_1rp.h,_1rp.i,_1rq.a,_1rq.b,_1ro.c,_1ro.d,_1ro.e,_1ro.f,_1rr.a,_1rr.b,_1ro.h,_1ro.i,_1ro.j,_1ro.k,_1ro.l,_1ro.m,_1ro.n,_1ro.o,_1ro.p,_1ro.q,_1ro.r,_1ro.s,_1ro.t,_1ro.u,_1ro.v,_)),_=wMV(_1qO,_1rs);return _7f;},_]));return _7f;}}},_1rt=function(_){var _1ru=__app1(E(_1),"canvas2"),_1rv=__eq(_1ru,E(_7));if(!E(_1rv)){var _1rw=__isUndef(_1ru);if(!E(_1rw)){return new F(function(){return _1qC(_,new T1(1,_1ru));});}else{return new F(function(){return _1qC(_,_0);});}}else{return new F(function(){return _1qC(_,_0);});}},_1rx=function(_){return new F(function(){return _1rt(_);});};
var hasteMain = function() {B(A(_1rx, [0]));};window.onload = hasteMain;