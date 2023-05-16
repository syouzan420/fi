"use strict";
var __haste_prog_id = '726a1339183241dc19ddfb10a54c5c75159bb8776edb763ef6577c7dbc7ab609';
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

var _0=__Z,_1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2=function(_){return new F(function(){return __jsNull();});},_3=function(_4){var _5=B(A1(_4,_));return E(_5);},_6=new T(function(){return B(_3(_2));}),_7=new T(function(){return E(_6);}),_8="metaKey",_9="shiftKey",_a="altKey",_b="ctrlKey",_c="keyCode",_d=function(_e,_){var _f=__get(_e,E(_c)),_g=__get(_e,E(_b)),_h=__get(_e,E(_a)),_i=__get(_e,E(_9)),_j=__get(_e,E(_8));return new T(function(){var _k=Number(_f),_l=jsTrunc(_k);return new T5(0,_l,E(_g),E(_h),E(_i),E(_j));});},_m=function(_n,_o,_){return new F(function(){return _d(E(_o),_);});},_p="keydown",_q="keyup",_r="keypress",_s=function(_t){switch(E(_t)){case 0:return E(_r);case 1:return E(_q);default:return E(_p);}},_u=new T2(0,_s,_m),_v="deltaZ",_w="deltaY",_x="deltaX",_y=function(_z,_A){var _B=E(_z);return (_B._==0)?E(_A):new T2(1,_B.a,new T(function(){return B(_y(_B.b,_A));}));},_C=function(_D,_E){var _F=jsShowI(_D);return new F(function(){return _y(fromJSStr(_F),_E);});},_G=41,_H=40,_I=function(_J,_K,_L){if(_K>=0){return new F(function(){return _C(_K,_L);});}else{if(_J<=6){return new F(function(){return _C(_K,_L);});}else{return new T2(1,_H,new T(function(){var _M=jsShowI(_K);return B(_y(fromJSStr(_M),new T2(1,_G,_L)));}));}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_I(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_I(0,_R,_P));}))));});},_S=function(_T,_){return new T(function(){var _U=Number(E(_T)),_V=jsTrunc(_U);if(_V<0){return B(_Q(_V));}else{if(_V>2){return B(_Q(_V));}else{return _V;}}});},_W=0,_X=new T3(0,_W,_W,_W),_Y="button",_Z=new T(function(){return eval("jsGetMouseCoords");}),_10=__Z,_11=function(_12,_){var _13=E(_12);if(!_13._){return _10;}else{var _14=B(_11(_13.b,_));return new T2(1,new T(function(){var _15=Number(E(_13.a));return jsTrunc(_15);}),_14);}},_16=function(_17,_){var _18=__arr2lst(0,_17);return new F(function(){return _11(_18,_);});},_19=function(_1a,_){return new F(function(){return _16(E(_1a),_);});},_1b=function(_1c,_){return new T(function(){var _1d=Number(E(_1c));return jsTrunc(_1d);});},_1e=new T2(0,_1b,_19),_1f=function(_1g,_){var _1h=E(_1g);if(!_1h._){return _10;}else{var _1i=B(_1f(_1h.b,_));return new T2(1,_1h.a,_1i);}},_1j=new T(function(){return B(unCStr("base"));}),_1k=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1l=new T(function(){return B(unCStr("IOException"));}),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1j,_1k,_1l),_1n=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1m,_10,_10),_1o=function(_1p){return E(_1n);},_1q=function(_1r){return E(E(_1r).a);},_1s=function(_1t,_1u,_1v){var _1w=B(A1(_1t,_)),_1x=B(A1(_1u,_)),_1y=hs_eqWord64(_1w.a,_1x.a);if(!_1y){return __Z;}else{var _1z=hs_eqWord64(_1w.b,_1x.b);return (!_1z)?__Z:new T1(1,_1v);}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1s(B(_1q(_1C.a)),_1o,_1C.b);});},_1D=new T(function(){return B(unCStr(": "));}),_1E=new T(function(){return B(unCStr(")"));}),_1F=new T(function(){return B(unCStr(" ("));}),_1G=new T(function(){return B(unCStr("interrupted"));}),_1H=new T(function(){return B(unCStr("system error"));}),_1I=new T(function(){return B(unCStr("unsatisified constraints"));}),_1J=new T(function(){return B(unCStr("user error"));}),_1K=new T(function(){return B(unCStr("permission denied"));}),_1L=new T(function(){return B(unCStr("illegal operation"));}),_1M=new T(function(){return B(unCStr("end of file"));}),_1N=new T(function(){return B(unCStr("resource exhausted"));}),_1O=new T(function(){return B(unCStr("resource busy"));}),_1P=new T(function(){return B(unCStr("does not exist"));}),_1Q=new T(function(){return B(unCStr("already exists"));}),_1R=new T(function(){return B(unCStr("resource vanished"));}),_1S=new T(function(){return B(unCStr("timeout"));}),_1T=new T(function(){return B(unCStr("unsupported operation"));}),_1U=new T(function(){return B(unCStr("hardware fault"));}),_1V=new T(function(){return B(unCStr("inappropriate type"));}),_1W=new T(function(){return B(unCStr("invalid argument"));}),_1X=new T(function(){return B(unCStr("failed"));}),_1Y=new T(function(){return B(unCStr("protocol error"));}),_1Z=function(_20,_21){switch(E(_20)){case 0:return new F(function(){return _y(_1Q,_21);});break;case 1:return new F(function(){return _y(_1P,_21);});break;case 2:return new F(function(){return _y(_1O,_21);});break;case 3:return new F(function(){return _y(_1N,_21);});break;case 4:return new F(function(){return _y(_1M,_21);});break;case 5:return new F(function(){return _y(_1L,_21);});break;case 6:return new F(function(){return _y(_1K,_21);});break;case 7:return new F(function(){return _y(_1J,_21);});break;case 8:return new F(function(){return _y(_1I,_21);});break;case 9:return new F(function(){return _y(_1H,_21);});break;case 10:return new F(function(){return _y(_1Y,_21);});break;case 11:return new F(function(){return _y(_1X,_21);});break;case 12:return new F(function(){return _y(_1W,_21);});break;case 13:return new F(function(){return _y(_1V,_21);});break;case 14:return new F(function(){return _y(_1U,_21);});break;case 15:return new F(function(){return _y(_1T,_21);});break;case 16:return new F(function(){return _y(_1S,_21);});break;case 17:return new F(function(){return _y(_1R,_21);});break;default:return new F(function(){return _y(_1G,_21);});}},_22=new T(function(){return B(unCStr("}"));}),_23=new T(function(){return B(unCStr("{handle: "));}),_24=function(_25,_26,_27,_28,_29,_2a){var _2b=new T(function(){var _2c=new T(function(){var _2d=new T(function(){var _2e=E(_28);if(!_2e._){return E(_2a);}else{var _2f=new T(function(){return B(_y(_2e,new T(function(){return B(_y(_1E,_2a));},1)));},1);return B(_y(_1F,_2f));}},1);return B(_1Z(_26,_2d));}),_2g=E(_27);if(!_2g._){return E(_2c);}else{return B(_y(_2g,new T(function(){return B(_y(_1D,_2c));},1)));}}),_2h=E(_29);if(!_2h._){var _2i=E(_25);if(!_2i._){return E(_2b);}else{var _2j=E(_2i.a);if(!_2j._){var _2k=new T(function(){var _2l=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2l));},1);return new F(function(){return _y(_23,_2k);});}else{var _2m=new T(function(){var _2n=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2n));},1);return new F(function(){return _y(_23,_2m);});}}}else{return new F(function(){return _y(_2h.a,new T(function(){return B(_y(_1D,_2b));},1));});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _24(_2q.a,_2q.b,_2q.c,_2q.d,_2q.f,_10);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _24(_2v.a,_2v.b,_2v.c,_2v.d,_2v.f,_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _24(_2z.a,_2z.b,_2z.c,_2z.d,_2z.f,_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H._){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=new T(function(){var _2J=new T(function(){var _2K=function(_2L){var _2M=E(_2L);if(!_2M._){return E(new T2(1,_2B,_2G));}else{var _2N=new T(function(){return B(A2(_2E,_2M.a,new T(function(){return B(_2K(_2M.b));})));});return new T2(1,_2A,_2N);}};return B(_2K(_2H.b));});return B(A2(_2E,_2H.a,_2J));});return new T2(1,_2C,_2I);}},_2O=function(_2P,_2Q){return new F(function(){return _2D(_2w,_2P,_2Q);});},_2R=new T3(0,_2r,_2o,_2O),_2S=new T(function(){return new T5(0,_1o,_2R,_2T,_1A,_2o);}),_2T=function(_2U){return new T2(0,_2S,_2U);},_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_0,_2V,_10,_2W,_0,_0),_2Y=new T(function(){return B(_2T(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1f(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_3d,_3e,_){if(E(_3d)==7){var _3f=__app1(E(_Z),_3e),_3g=B(_32(_1e,_1e,_3f,_)),_3h=__get(_3e,E(_x)),_3i=__get(_3e,E(_w)),_3j=__get(_3e,E(_v));return new T(function(){return new T3(0,E(_3g),E(_0),E(new T3(0,_3h,_3i,_3j)));});}else{var _3k=__app1(E(_Z),_3e),_3l=B(_32(_1e,_1e,_3k,_)),_3m=__get(_3e,E(_Y)),_3n=__eq(_3m,E(_7));if(!E(_3n)){var _3o=__isUndef(_3m);if(!E(_3o)){var _3p=B(_S(_3m,_));return new T(function(){return new T3(0,E(_3l),E(new T1(1,_3p)),E(_X));});}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}},_3q=function(_3r,_3s,_){return new F(function(){return _3c(_3r,E(_3s),_);});},_3t="mouseout",_3u="mouseover",_3v="mousemove",_3w="mouseup",_3x="mousedown",_3y="dblclick",_3z="click",_3A="wheel",_3B=function(_3C){switch(E(_3C)){case 0:return E(_3z);case 1:return E(_3y);case 2:return E(_3x);case 3:return E(_3w);case 4:return E(_3v);case 5:return E(_3u);case 6:return E(_3t);default:return E(_3A);}},_3D=new T2(0,_3B,_3q),_3E=function(_3F){return E(_3F);},_3G=function(_3H,_3I){return E(_3H)==E(_3I);},_3J=function(_3K,_3L){return E(_3K)!=E(_3L);},_3M=new T2(0,_3G,_3J),_3N="screenY",_3O="screenX",_3P="clientY",_3Q="clientX",_3R="pageY",_3S="pageX",_3T="target",_3U="identifier",_3V=function(_3W,_){var _3X=__get(_3W,E(_3U)),_3Y=__get(_3W,E(_3T)),_3Z=__get(_3W,E(_3S)),_40=__get(_3W,E(_3R)),_41=__get(_3W,E(_3Q)),_42=__get(_3W,E(_3P)),_43=__get(_3W,E(_3O)),_44=__get(_3W,E(_3N));return new T(function(){var _45=Number(_3X),_46=jsTrunc(_45);return new T5(0,_46,_3Y,E(new T2(0,new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}),new T(function(){var _48=Number(_40);return jsTrunc(_48);}))),E(new T2(0,new T(function(){var _49=Number(_41);return jsTrunc(_49);}),new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}))),E(new T2(0,new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}),new T(function(){var _4c=Number(_44);return jsTrunc(_4c);}))));});},_4d=function(_4e,_){var _4f=E(_4e);if(!_4f._){return _10;}else{var _4g=B(_3V(E(_4f.a),_)),_4h=B(_4d(_4f.b,_));return new T2(1,_4g,_4h);}},_4i="touches",_4j=function(_4k){return E(E(_4k).b);},_4l=function(_4m,_4n,_){var _4o=__arr2lst(0,_4n),_4p=new T(function(){return B(_4j(_4m));}),_4q=function(_4r,_){var _4s=E(_4r);if(!_4s._){return _10;}else{var _4t=B(A2(_4p,_4s.a,_)),_4u=B(_4q(_4s.b,_));return new T2(1,_4t,_4u);}};return new F(function(){return _4q(_4o,_);});},_4v=function(_4w,_){return new F(function(){return _4l(_1e,E(_4w),_);});},_4x=new T2(0,_19,_4v),_4y=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4z=function(_4A){return E(E(_4A).a);},_4B=function(_4C,_4D,_4E){while(1){var _4F=E(_4E);if(!_4F._){return false;}else{if(!B(A3(_4z,_4C,_4D,_4F.a))){_4E=_4F.b;continue;}else{return true;}}}},_4G=function(_4H,_4I){while(1){var _4J=B((function(_4K,_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{var _4N=_4M.a,_4O=_4M.b;if(!B(A1(_4K,_4N))){var _4P=_4K;_4H=_4P;_4I=_4O;return __continue;}else{return new T2(1,_4N,new T(function(){return B(_4G(_4K,_4O));}));}}})(_4H,_4I));if(_4J!=__continue){return _4J;}}},_4Q=function(_4R,_){var _4S=__get(_4R,E(_4i)),_4T=__arr2lst(0,_4S),_4U=B(_4d(_4T,_)),_4V=__app1(E(_4y),_4R),_4W=B(_32(_4x,_4x,_4V,_)),_4X=E(_4W),_4Y=new T(function(){var _4Z=function(_50){return new F(function(){return _4B(_3M,new T(function(){return E(_50).a;}),_4X.a);});};return B(_4G(_4Z,_4U));}),_51=new T(function(){var _52=function(_53){return new F(function(){return _4B(_3M,new T(function(){return E(_53).a;}),_4X.b);});};return B(_4G(_52,_4U));});return new T3(0,_4U,_51,_4Y);},_54=function(_55,_56,_){return new F(function(){return _4Q(E(_56),_);});},_57="touchcancel",_58="touchend",_59="touchmove",_5a="touchstart",_5b=function(_5c){switch(E(_5c)){case 0:return E(_5a);case 1:return E(_59);case 2:return E(_58);default:return E(_57);}},_5d=new T2(0,_5b,_54),_5e=function(_5f,_5g,_){var _5h=B(A1(_5f,_)),_5i=B(A1(_5g,_));return _5h;},_5j=function(_5k,_5l,_){var _5m=B(A1(_5k,_)),_5n=B(A1(_5l,_));return new T(function(){return B(A1(_5m,_5n));});},_5o=function(_5p,_5q,_){var _5r=B(A1(_5q,_));return _5p;},_5s=function(_5t,_5u,_){var _5v=B(A1(_5u,_));return new T(function(){return B(A1(_5t,_5v));});},_5w=new T2(0,_5s,_5o),_5x=function(_5y,_){return _5y;},_5z=function(_5A,_5B,_){var _5C=B(A1(_5A,_));return new F(function(){return A1(_5B,_);});},_5D=new T5(0,_5w,_5x,_5j,_5z,_5e),_5E=new T(function(){return E(_2S);}),_5F=function(_5G){return E(E(_5G).c);},_5H=function(_5I){return new T6(0,_0,_2V,_10,_5I,_0,_0);},_5J=function(_5K,_){var _5L=new T(function(){return B(A2(_5F,_5E,new T(function(){return B(A1(_5H,_5K));})));});return new F(function(){return die(_5L);});},_5M=function(_5N,_){return new F(function(){return _5J(_5N,_);});},_5O=function(_5P){return new F(function(){return A1(_5M,_5P);});},_5Q=function(_5R,_5S,_){var _5T=B(A1(_5R,_));return new F(function(){return A2(_5S,_5T,_);});},_5U=new T5(0,_5D,_5Q,_5z,_5x,_5O),_5V=function(_5W){return E(_5W);},_5X=new T2(0,_5U,_5V),_5Y=new T2(0,_5X,_5x),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_60=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_61=new T(function(){return eval("(function(cv){return cv.height})");}),_62=new T(function(){return eval("(function(cv){return cv.width})");}),_63=function(_64,_){var _65=__app1(E(_62),_64),_66=__app1(E(_61),_64),_67=__app1(E(_60),_64),_68=__app1(E(_5Z),_64);return new T2(0,new T(function(){return _65/_67;}),new T(function(){return _66/_68;}));},_69=function(_6a,_6b){return E(_6a)!=E(_6b);},_6c=function(_6d,_6e){return E(_6d)==E(_6e);},_6f=new T2(0,_6c,_69),_6g=function(_6h,_6i,_6j){while(1){var _6k=E(_6i);if(!_6k._){return (E(_6j)._==0)?true:false;}else{var _6l=E(_6j);if(!_6l._){return false;}else{if(!B(A3(_4z,_6h,_6k.a,_6l.a))){return false;}else{_6i=_6k.b;_6j=_6l.b;continue;}}}}},_6m=function(_6n,_6o,_6p){return new F(function(){return A1(_6n,new T2(1,_2A,new T(function(){return B(A1(_6o,_6p));})));});},_6q=function(_6r,_6s){switch(E(_6r)){case 0:return (E(_6s)==0)?true:false;case 1:return (E(_6s)==1)?true:false;case 2:return (E(_6s)==2)?true:false;case 3:return (E(_6s)==3)?true:false;case 4:return (E(_6s)==4)?true:false;case 5:return (E(_6s)==5)?true:false;case 6:return (E(_6s)==6)?true:false;case 7:return (E(_6s)==7)?true:false;default:return (E(_6s)==8)?true:false;}},_6t=function(_6u,_6v,_6w,_6x){if(_6u!=_6w){return false;}else{return new F(function(){return _6q(_6v,_6x);});}},_6y=function(_6z,_6A){var _6B=E(_6z),_6C=E(_6A);return new F(function(){return _6t(E(_6B.a),_6B.b,E(_6C.a),_6C.b);});},_6D=function(_6E,_6F,_6G,_6H){if(_6E!=_6G){return true;}else{switch(E(_6F)){case 0:return (E(_6H)==0)?false:true;case 1:return (E(_6H)==1)?false:true;case 2:return (E(_6H)==2)?false:true;case 3:return (E(_6H)==3)?false:true;case 4:return (E(_6H)==4)?false:true;case 5:return (E(_6H)==5)?false:true;case 6:return (E(_6H)==6)?false:true;case 7:return (E(_6H)==7)?false:true;default:return (E(_6H)==8)?false:true;}}},_6I=function(_6J,_6K){var _6L=E(_6J),_6M=E(_6K);return new F(function(){return _6D(E(_6L.a),_6L.b,E(_6M.a),_6M.b);});},_6N=new T2(0,_6y,_6I),_6O=function(_6P,_6Q){return (!B(_6g(_6N,_6P,_6Q)))?true:false;},_6R=function(_6S,_6T){return new F(function(){return _6g(_6N,_6S,_6T);});},_6U=new T2(0,_6R,_6O),_6V=new T(function(){return B(unCStr("!!: negative index"));}),_6W=new T(function(){return B(unCStr("Prelude."));}),_6X=new T(function(){return B(_y(_6W,_6V));}),_6Y=new T(function(){return B(err(_6X));}),_6Z=new T(function(){return B(unCStr("!!: index too large"));}),_70=new T(function(){return B(_y(_6W,_6Z));}),_71=new T(function(){return B(err(_70));}),_72=function(_73,_74){while(1){var _75=E(_73);if(!_75._){return E(_71);}else{var _76=E(_74);if(!_76){return E(_75.a);}else{_73=_75.b;_74=_76-1|0;continue;}}}},_77=function(_78,_79){if(_79>=0){return new F(function(){return _72(_78,_79);});}else{return E(_6Y);}},_7a=function(_7b,_7c){while(1){var _7d=E(_7b);if(!_7d._){return E(_7c);}else{var _7e=_7c+1|0;_7b=_7d.b;_7c=_7e;continue;}}},_7f=0,_7g=function(_){return _7f;},_7h=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_7i=function(_7j,_7k,_7l){var _7m=new T(function(){return toJSStr(E(_7l));});return function(_7n,_){var _7o=__app4(E(_7h),E(_7n),E(_7m),E(_7j),E(_7k));return new F(function(){return _7g(_);});};},_7p=new T1(0,1),_7q=function(_7r,_7s){var _7t=E(_7r);if(!_7t._){var _7u=_7t.a,_7v=E(_7s);if(!_7v._){var _7w=_7v.a;return (_7u!=_7w)?(_7u>_7w)?2:0:1;}else{var _7x=I_compareInt(_7v.a,_7u);return (_7x<=0)?(_7x>=0)?1:2:0;}}else{var _7y=_7t.a,_7z=E(_7s);if(!_7z._){var _7A=I_compareInt(_7y,_7z.a);return (_7A>=0)?(_7A<=0)?1:2:0;}else{var _7B=I_compare(_7y,_7z.a);return (_7B>=0)?(_7B<=0)?1:2:0;}}},_7C=new T(function(){return B(unCStr("base"));}),_7D=new T(function(){return B(unCStr("GHC.Exception"));}),_7E=new T(function(){return B(unCStr("ArithException"));}),_7F=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7C,_7D,_7E),_7G=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7F,_10,_10),_7H=function(_7I){return E(_7G);},_7J=function(_7K){var _7L=E(_7K);return new F(function(){return _1s(B(_1q(_7L.a)),_7H,_7L.b);});},_7M=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_7N=new T(function(){return B(unCStr("denormal"));}),_7O=new T(function(){return B(unCStr("divide by zero"));}),_7P=new T(function(){return B(unCStr("loss of precision"));}),_7Q=new T(function(){return B(unCStr("arithmetic underflow"));}),_7R=new T(function(){return B(unCStr("arithmetic overflow"));}),_7S=function(_7T,_7U){switch(E(_7T)){case 0:return new F(function(){return _y(_7R,_7U);});break;case 1:return new F(function(){return _y(_7Q,_7U);});break;case 2:return new F(function(){return _y(_7P,_7U);});break;case 3:return new F(function(){return _y(_7O,_7U);});break;case 4:return new F(function(){return _y(_7N,_7U);});break;default:return new F(function(){return _y(_7M,_7U);});}},_7V=function(_7W){return new F(function(){return _7S(_7W,_10);});},_7X=function(_7Y,_7Z,_80){return new F(function(){return _7S(_7Z,_80);});},_81=function(_82,_83){return new F(function(){return _2D(_7S,_82,_83);});},_84=new T3(0,_7X,_7V,_81),_85=new T(function(){return new T5(0,_7H,_84,_86,_7J,_7V);}),_86=function(_87){return new T2(0,_85,_87);},_88=3,_89=new T(function(){return B(_86(_88));}),_8a=new T(function(){return die(_89);}),_8b=function(_8c,_8d){var _8e=E(_8c);return (_8e._==0)?_8e.a*Math.pow(2,_8d):I_toNumber(_8e.a)*Math.pow(2,_8d);},_8f=function(_8g,_8h){var _8i=E(_8g);if(!_8i._){var _8j=_8i.a,_8k=E(_8h);return (_8k._==0)?_8j==_8k.a:(I_compareInt(_8k.a,_8j)==0)?true:false;}else{var _8l=_8i.a,_8m=E(_8h);return (_8m._==0)?(I_compareInt(_8l,_8m.a)==0)?true:false:(I_compare(_8l,_8m.a)==0)?true:false;}},_8n=function(_8o){var _8p=E(_8o);if(!_8p._){return E(_8p.a);}else{return new F(function(){return I_toInt(_8p.a);});}},_8q=function(_8r,_8s){while(1){var _8t=E(_8r);if(!_8t._){var _8u=_8t.a,_8v=E(_8s);if(!_8v._){var _8w=_8v.a,_8x=addC(_8u,_8w);if(!E(_8x.b)){return new T1(0,_8x.a);}else{_8r=new T1(1,I_fromInt(_8u));_8s=new T1(1,I_fromInt(_8w));continue;}}else{_8r=new T1(1,I_fromInt(_8u));_8s=_8v;continue;}}else{var _8y=E(_8s);if(!_8y._){_8r=_8t;_8s=new T1(1,I_fromInt(_8y.a));continue;}else{return new T1(1,I_add(_8t.a,_8y.a));}}}},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C._){var _8D=E(_8C.a);if(_8D==( -2147483648)){_8A=new T1(1,I_fromInt( -2147483648));continue;}else{var _8E=E(_8B);if(!_8E._){var _8F=_8E.a;return new T2(0,new T1(0,quot(_8D,_8F)),new T1(0,_8D%_8F));}else{_8A=new T1(1,I_fromInt(_8D));_8B=_8E;continue;}}}else{var _8G=E(_8B);if(!_8G._){_8A=_8C;_8B=new T1(1,I_fromInt(_8G.a));continue;}else{var _8H=I_quotRem(_8C.a,_8G.a);return new T2(0,new T1(1,_8H.a),new T1(1,_8H.b));}}}},_8I=new T1(0,0),_8J=function(_8K,_8L){while(1){var _8M=E(_8K);if(!_8M._){_8K=new T1(1,I_fromInt(_8M.a));continue;}else{return new T1(1,I_shiftLeft(_8M.a,_8L));}}},_8N=function(_8O,_8P,_8Q){if(!B(_8f(_8Q,_8I))){var _8R=B(_8z(_8P,_8Q)),_8S=_8R.a;switch(B(_7q(B(_8J(_8R.b,1)),_8Q))){case 0:return new F(function(){return _8b(_8S,_8O);});break;case 1:if(!(B(_8n(_8S))&1)){return new F(function(){return _8b(_8S,_8O);});}else{return new F(function(){return _8b(B(_8q(_8S,_7p)),_8O);});}break;default:return new F(function(){return _8b(B(_8q(_8S,_7p)),_8O);});}}else{return E(_8a);}},_8T=function(_8U,_8V){var _8W=E(_8U);if(!_8W._){var _8X=_8W.a,_8Y=E(_8V);return (_8Y._==0)?_8X>_8Y.a:I_compareInt(_8Y.a,_8X)<0;}else{var _8Z=_8W.a,_90=E(_8V);return (_90._==0)?I_compareInt(_8Z,_90.a)>0:I_compare(_8Z,_90.a)>0;}},_91=new T1(0,1),_92=function(_93,_94){var _95=E(_93);if(!_95._){var _96=_95.a,_97=E(_94);return (_97._==0)?_96<_97.a:I_compareInt(_97.a,_96)>0;}else{var _98=_95.a,_99=E(_94);return (_99._==0)?I_compareInt(_98,_99.a)<0:I_compare(_98,_99.a)<0;}},_9a=new T(function(){return B(unCStr("base"));}),_9b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_9c=new T(function(){return B(unCStr("PatternMatchFail"));}),_9d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9a,_9b,_9c),_9e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9d,_10,_10),_9f=function(_9g){return E(_9e);},_9h=function(_9i){var _9j=E(_9i);return new F(function(){return _1s(B(_1q(_9j.a)),_9f,_9j.b);});},_9k=function(_9l){return E(E(_9l).a);},_9m=function(_9n){return new T2(0,_9o,_9n);},_9p=function(_9q,_9r){return new F(function(){return _y(E(_9q).a,_9r);});},_9s=function(_9t,_9u){return new F(function(){return _2D(_9p,_9t,_9u);});},_9v=function(_9w,_9x,_9y){return new F(function(){return _y(E(_9x).a,_9y);});},_9z=new T3(0,_9v,_9k,_9s),_9o=new T(function(){return new T5(0,_9f,_9z,_9m,_9h,_9k);}),_9A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_9B=function(_9C,_9D){return new F(function(){return die(new T(function(){return B(A2(_5F,_9D,_9C));}));});},_9E=function(_9F,_87){return new F(function(){return _9B(_9F,_87);});},_9G=function(_9H,_9I){var _9J=E(_9I);if(!_9J._){return new T2(0,_10,_10);}else{var _9K=_9J.a;if(!B(A1(_9H,_9K))){return new T2(0,_10,_9J);}else{var _9L=new T(function(){var _9M=B(_9G(_9H,_9J.b));return new T2(0,_9M.a,_9M.b);});return new T2(0,new T2(1,_9K,new T(function(){return E(E(_9L).a);})),new T(function(){return E(E(_9L).b);}));}}},_9N=32,_9O=new T(function(){return B(unCStr("\n"));}),_9P=function(_9Q){return (E(_9Q)==124)?false:true;},_9R=function(_9S,_9T){var _9U=B(_9G(_9P,B(unCStr(_9S)))),_9V=_9U.a,_9W=function(_9X,_9Y){var _9Z=new T(function(){var _a0=new T(function(){return B(_y(_9T,new T(function(){return B(_y(_9Y,_9O));},1)));});return B(unAppCStr(": ",_a0));},1);return new F(function(){return _y(_9X,_9Z);});},_a1=E(_9U.b);if(!_a1._){return new F(function(){return _9W(_9V,_10);});}else{if(E(_a1.a)==124){return new F(function(){return _9W(_9V,new T2(1,_9N,_a1.b));});}else{return new F(function(){return _9W(_9V,_10);});}}},_a2=function(_a3){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9R(_a3,_9A));})),_9o);});},_a4=function(_a5){var _a6=function(_a7,_a8){while(1){if(!B(_92(_a7,_a5))){if(!B(_8T(_a7,_a5))){if(!B(_8f(_a7,_a5))){return new F(function(){return _a2("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_a8);}}else{return _a8-1|0;}}else{var _a9=B(_8J(_a7,1)),_aa=_a8+1|0;_a7=_a9;_a8=_aa;continue;}}};return new F(function(){return _a6(_91,0);});},_ab=function(_ac){var _ad=E(_ac);if(!_ad._){var _ae=_ad.a>>>0;if(!_ae){return  -1;}else{var _af=function(_ag,_ah){while(1){if(_ag>=_ae){if(_ag<=_ae){if(_ag!=_ae){return new F(function(){return _a2("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ah);}}else{return _ah-1|0;}}else{var _ai=imul(_ag,2)>>>0,_aj=_ah+1|0;_ag=_ai;_ah=_aj;continue;}}};return new F(function(){return _af(1,0);});}}else{return new F(function(){return _a4(_ad);});}},_ak=function(_al){var _am=E(_al);if(!_am._){var _an=_am.a>>>0;if(!_an){return new T2(0, -1,0);}else{var _ao=function(_ap,_aq){while(1){if(_ap>=_an){if(_ap<=_an){if(_ap!=_an){return new F(function(){return _a2("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_aq);}}else{return _aq-1|0;}}else{var _ar=imul(_ap,2)>>>0,_as=_aq+1|0;_ap=_ar;_aq=_as;continue;}}};return new T2(0,B(_ao(1,0)),(_an&_an-1>>>0)>>>0&4294967295);}}else{var _at=_am.a;return new T2(0,B(_ab(_am)),I_compareInt(I_and(_at,I_sub(_at,I_fromInt(1))),0));}},_au=function(_av,_aw){var _ax=E(_av);if(!_ax._){var _ay=_ax.a,_az=E(_aw);return (_az._==0)?_ay<=_az.a:I_compareInt(_az.a,_ay)>=0;}else{var _aA=_ax.a,_aB=E(_aw);return (_aB._==0)?I_compareInt(_aA,_aB.a)<=0:I_compare(_aA,_aB.a)<=0;}},_aC=function(_aD,_aE){while(1){var _aF=E(_aD);if(!_aF._){var _aG=_aF.a,_aH=E(_aE);if(!_aH._){return new T1(0,(_aG>>>0&_aH.a>>>0)>>>0&4294967295);}else{_aD=new T1(1,I_fromInt(_aG));_aE=_aH;continue;}}else{var _aI=E(_aE);if(!_aI._){_aD=_aF;_aE=new T1(1,I_fromInt(_aI.a));continue;}else{return new T1(1,I_and(_aF.a,_aI.a));}}}},_aJ=function(_aK,_aL){while(1){var _aM=E(_aK);if(!_aM._){var _aN=_aM.a,_aO=E(_aL);if(!_aO._){var _aP=_aO.a,_aQ=subC(_aN,_aP);if(!E(_aQ.b)){return new T1(0,_aQ.a);}else{_aK=new T1(1,I_fromInt(_aN));_aL=new T1(1,I_fromInt(_aP));continue;}}else{_aK=new T1(1,I_fromInt(_aN));_aL=_aO;continue;}}else{var _aR=E(_aL);if(!_aR._){_aK=_aM;_aL=new T1(1,I_fromInt(_aR.a));continue;}else{return new T1(1,I_sub(_aM.a,_aR.a));}}}},_aS=new T1(0,2),_aT=function(_aU,_aV){var _aW=E(_aU);if(!_aW._){var _aX=(_aW.a>>>0&(2<<_aV>>>0)-1>>>0)>>>0,_aY=1<<_aV>>>0;return (_aY<=_aX)?(_aY>=_aX)?1:2:0;}else{var _aZ=B(_aC(_aW,B(_aJ(B(_8J(_aS,_aV)),_91)))),_b0=B(_8J(_91,_aV));return (!B(_8T(_b0,_aZ)))?(!B(_92(_b0,_aZ)))?1:2:0;}},_b1=function(_b2,_b3){while(1){var _b4=E(_b2);if(!_b4._){_b2=new T1(1,I_fromInt(_b4.a));continue;}else{return new T1(1,I_shiftRight(_b4.a,_b3));}}},_b5=function(_b6,_b7,_b8,_b9){var _ba=B(_ak(_b9)),_bb=_ba.a;if(!E(_ba.b)){var _bc=B(_ab(_b8));if(_bc<((_bb+_b6|0)-1|0)){var _bd=_bb+(_b6-_b7|0)|0;if(_bd>0){if(_bd>_bc){if(_bd<=(_bc+1|0)){if(!E(B(_ak(_b8)).b)){return 0;}else{return new F(function(){return _8b(_7p,_b6-_b7|0);});}}else{return 0;}}else{var _be=B(_b1(_b8,_bd));switch(B(_aT(_b8,_bd-1|0))){case 0:return new F(function(){return _8b(_be,_b6-_b7|0);});break;case 1:if(!(B(_8n(_be))&1)){return new F(function(){return _8b(_be,_b6-_b7|0);});}else{return new F(function(){return _8b(B(_8q(_be,_7p)),_b6-_b7|0);});}break;default:return new F(function(){return _8b(B(_8q(_be,_7p)),_b6-_b7|0);});}}}else{return new F(function(){return _8b(_b8,(_b6-_b7|0)-_bd|0);});}}else{if(_bc>=_b7){var _bf=B(_b1(_b8,(_bc+1|0)-_b7|0));switch(B(_aT(_b8,_bc-_b7|0))){case 0:return new F(function(){return _8b(_bf,((_bc-_bb|0)+1|0)-_b7|0);});break;case 2:return new F(function(){return _8b(B(_8q(_bf,_7p)),((_bc-_bb|0)+1|0)-_b7|0);});break;default:if(!(B(_8n(_bf))&1)){return new F(function(){return _8b(_bf,((_bc-_bb|0)+1|0)-_b7|0);});}else{return new F(function(){return _8b(B(_8q(_bf,_7p)),((_bc-_bb|0)+1|0)-_b7|0);});}}}else{return new F(function(){return _8b(_b8, -_bb);});}}}else{var _bg=B(_ab(_b8))-_bb|0,_bh=function(_bi){var _bj=function(_bk,_bl){if(!B(_au(B(_8J(_bl,_b7)),_bk))){return new F(function(){return _8N(_bi-_b7|0,_bk,_bl);});}else{return new F(function(){return _8N((_bi-_b7|0)+1|0,_bk,B(_8J(_bl,1)));});}};if(_bi>=_b7){if(_bi!=_b7){return new F(function(){return _bj(_b8,new T(function(){return B(_8J(_b9,_bi-_b7|0));}));});}else{return new F(function(){return _bj(_b8,_b9);});}}else{return new F(function(){return _bj(new T(function(){return B(_8J(_b8,_b7-_bi|0));}),_b9);});}};if(_b6>_bg){return new F(function(){return _bh(_b6);});}else{return new F(function(){return _bh(_bg);});}}},_bm=new T1(0,2147483647),_bn=new T(function(){return B(_8q(_bm,_91));}),_bo=function(_bp){var _bq=E(_bp);if(!_bq._){var _br=E(_bq.a);return (_br==( -2147483648))?E(_bn):new T1(0, -_br);}else{return new T1(1,I_negate(_bq.a));}},_bs=new T(function(){return 0/0;}),_bt=new T(function(){return  -1/0;}),_bu=new T(function(){return 1/0;}),_bv=0,_bw=function(_bx,_by){if(!B(_8f(_by,_8I))){if(!B(_8f(_bx,_8I))){if(!B(_92(_bx,_8I))){return new F(function(){return _b5( -1021,53,_bx,_by);});}else{return  -B(_b5( -1021,53,B(_bo(_bx)),_by));}}else{return E(_bv);}}else{return (!B(_8f(_bx,_8I)))?(!B(_92(_bx,_8I)))?E(_bu):E(_bt):E(_bs);}},_bz=function(_bA){var _bB=E(_bA);return new F(function(){return _bw(_bB.a,_bB.b);});},_bC=function(_bD){return 1/E(_bD);},_bE=function(_bF){var _bG=E(_bF);return (_bG!=0)?(_bG<=0)? -_bG:E(_bG):E(_bv);},_bH=function(_bI){var _bJ=E(_bI);if(!_bJ._){return _bJ.a;}else{return new F(function(){return I_toNumber(_bJ.a);});}},_bK=function(_bL){return new F(function(){return _bH(_bL);});},_bM=1,_bN= -1,_bO=function(_bP){var _bQ=E(_bP);return (_bQ<=0)?(_bQ>=0)?E(_bQ):E(_bN):E(_bM);},_bR=function(_bS,_bT){return E(_bS)-E(_bT);},_bU=function(_bV){return  -E(_bV);},_bW=function(_bX,_bY){return E(_bX)+E(_bY);},_bZ=function(_c0,_c1){return E(_c0)*E(_c1);},_c2={_:0,a:_bW,b:_bR,c:_bZ,d:_bU,e:_bE,f:_bO,g:_bK},_c3=function(_c4,_c5){return E(_c4)/E(_c5);},_c6=new T4(0,_c2,_c3,_bC,_bz),_c7=new T1(0,1),_c8=function(_c9){return E(E(_c9).a);},_ca=function(_cb){return E(E(_cb).a);},_cc=function(_cd){return E(E(_cd).g);},_ce=function(_cf,_cg){var _ch=E(_cg),_ci=new T(function(){var _cj=B(_c8(_cf)),_ck=B(_ce(_cf,B(A3(_ca,_cj,_ch,new T(function(){return B(A2(_cc,_cj,_c7));})))));return new T2(1,_ck.a,_ck.b);});return new T2(0,_ch,_ci);},_cl=0,_cm=new T(function(){var _cn=B(_ce(_c6,_cl));return new T2(1,_cn.a,_cn.b);}),_co=new T(function(){return B(unCStr("px Unifont"));}),_cp=new T(function(){return B(_I(0,20,_10));}),_cq=new T(function(){return B(_y(_cp,_co));}),_cr=function(_cs,_){return _7f;},_ct=",",_cu="rgba(",_cv=new T(function(){return toJSStr(_10);}),_cw="rgb(",_cx=")",_cy=new T2(1,_cx,_10),_cz=function(_cA){var _cB=E(_cA);if(!_cB._){var _cC=jsCat(new T2(1,_cw,new T2(1,new T(function(){return String(_cB.a);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.b);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.c);}),_cy)))))),E(_cv));return E(_cC);}else{var _cD=jsCat(new T2(1,_cu,new T2(1,new T(function(){return String(_cB.a);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.b);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.c);}),new T2(1,_ct,new T2(1,new T(function(){return String(_cB.d);}),_cy)))))))),E(_cv));return E(_cD);}},_cE="strokeStyle",_cF="fillStyle",_cG=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_cH=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_cI=function(_cJ,_cK){var _cL=new T(function(){return B(_cz(_cJ));});return function(_cM,_){var _cN=E(_cM),_cO=E(_cF),_cP=E(_cG),_cQ=__app2(_cP,_cN,_cO),_cR=E(_cE),_cS=__app2(_cP,_cN,_cR),_cT=E(_cL),_cU=E(_cH),_cV=__app3(_cU,_cN,_cO,_cT),_cW=__app3(_cU,_cN,_cR,_cT),_cX=B(A2(_cK,_cN,_)),_cY=String(_cQ),_cZ=__app3(_cU,_cN,_cO,_cY),_d0=String(_cS),_d1=__app3(_cU,_cN,_cR,_d0);return new F(function(){return _7g(_);});};},_d2="font",_d3=function(_d4,_d5){var _d6=new T(function(){return toJSStr(E(_d4));});return function(_d7,_){var _d8=E(_d7),_d9=E(_d2),_da=__app2(E(_cG),_d8,_d9),_db=E(_cH),_dc=__app3(_db,_d8,_d9,E(_d6)),_dd=B(A2(_d5,_d8,_)),_de=String(_da),_df=__app3(_db,_d8,_d9,_de);return new F(function(){return _7g(_);});};},_dg=function(_dh,_di,_dj,_dk,_dl){var _dm=new T(function(){return E(_dj)*16;}),_dn=new T(function(){return E(_dk)*20;}),_do=function(_dp,_dq){var _dr=E(_dp);if(!_dr._){return E(_cr);}else{var _ds=E(_dq);if(!_ds._){return E(_cr);}else{var _dt=new T(function(){return B(_do(_dr.b,_ds.b));}),_du=new T(function(){var _dv=new T(function(){var _dw=new T(function(){return B(_7i(new T(function(){return E(_dm)+16*E(_ds.a);}),_dn,new T2(1,_dr.a,_10)));});return B(_d3(_cq,_dw));});return B(_cI(_di,_dv));});return function(_dx,_){var _dy=B(A2(_du,_dx,_));return new F(function(){return A2(_dt,_dx,_);});};}}};return new F(function(){return A3(_do,_dl,_cm,_dh);});},_dz=45,_dA=new T(function(){return B(unCStr("-"));}),_dB=new T2(1,_dz,_dA),_dC=function(_dD){var _dE=E(_dD);return (_dE==1)?E(_dB):new T2(1,_dz,new T(function(){return B(_dC(_dE-1|0));}));},_dF=new T(function(){return B(unCStr(": empty list"));}),_dG=function(_dH){return new F(function(){return err(B(_y(_6W,new T(function(){return B(_y(_dH,_dF));},1))));});},_dI=new T(function(){return B(unCStr("head"));}),_dJ=new T(function(){return B(_dG(_dI));}),_dK=new T(function(){return eval("(function(e){e.width = e.width;})");}),_dL=new T3(0,0,0,0),_dM=new T(function(){return B(_7i(_cl,_cl,_10));}),_dN=32,_dO=new T(function(){return B(unCStr("|"));}),_dP=function(_dQ){var _dR=E(_dQ);return (_dR._==0)?E(_dO):new T2(1,new T(function(){var _dS=E(_dR.a);switch(E(_dS.b)){case 7:return E(_dN);break;case 8:return E(_dN);break;default:return E(_dS.a);}}),new T(function(){return B(_dP(_dR.b));}));},_dT=function(_dU,_dV,_dW,_dX,_dY,_){var _dZ=__app1(E(_dK),_dV),_e0=B(A2(_dM,_dU,_)),_e1=B(unAppCStr("-",new T(function(){var _e2=E(_dY);if(!_e2._){return E(_dJ);}else{var _e3=B(_7a(_e2.a,0));if(0>=_e3){return E(_dA);}else{return B(_dC(_e3));}}}))),_e4=B(A(_dg,[_dU,_dL,_dW,_dX,_e1,_])),_e5=function(_e6,_e7,_e8,_){while(1){var _e9=B((function(_ea,_eb,_ec,_){var _ed=E(_ec);if(!_ed._){return new F(function(){return A(_dg,[_dU,_dL,_ea,_eb,_e1,_]);});}else{var _ee=B(A(_dg,[_dU,_dL,_ea,_eb,B(unAppCStr("|",new T(function(){return B(_dP(_ed.a));}))),_])),_ef=_ea;_e6=_ef;_e7=new T(function(){return E(_eb)+1|0;});_e8=_ed.b;return __continue;}})(_e6,_e7,_e8,_));if(_e9!=__continue){return _e9;}}};return new F(function(){return _e5(_dW,new T(function(){return E(_dX)+1|0;}),_dY,_);});},_eg=new T3(0,153,255,255),_eh=new T2(1,_eg,_10),_ei=new T3(0,255,153,204),_ej=new T2(1,_ei,_eh),_ek=new T3(0,255,204,153),_el=new T2(1,_ek,_ej),_em=new T2(1,_dL,_el),_en=new T(function(){return B(_77(_em,1));}),_eo=new T(function(){return B(_77(_em,2));}),_ep=2,_eq=function(_er){return E(_er).d;},_es=function(_et,_eu,_ev,_){var _ew=__app1(E(_dK),_eu),_ex=B(A2(_dM,_et,_)),_ey=new T(function(){return E(E(E(_ev).b).a);}),_ez=B(_dT(_et,_eu,new T(function(){return 26-E(_ey)|0;}),_ep,new T(function(){return E(E(_ev).c);}),_)),_eA=new T(function(){return E(E(_ev).a);});return new F(function(){return A(_dg,[_et,new T(function(){if(E(E(_ev).e)==32){return E(_en);}else{return E(_eo);}}),new T(function(){return ((E(E(_eA).a)+1|0)+26|0)-E(_ey)|0;},1),new T(function(){return (E(E(_eA).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_eq(_ev));}),_10),_]);});},_eB=function(_eC,_eD){while(1){var _eE=E(_eD);if(!_eE._){return __Z;}else{var _eF=_eE.b,_eG=E(_eC);if(_eG==1){return E(_eF);}else{_eC=_eG-1|0;_eD=_eF;continue;}}}},_eH=function(_eI,_eJ){var _eK=E(_eJ);if(!_eK._){return __Z;}else{var _eL=_eK.a,_eM=E(_eI);return (_eM==1)?new T2(1,_eL,_10):new T2(1,_eL,new T(function(){return B(_eH(_eM-1|0,_eK.b));}));}},_eN=function(_eO,_eP,_eQ,_eR){while(1){if(B(_77(new T2(1,_eQ,_eR),_eP))!=_eO){var _eS=_eP+1|0;_eP=_eS;continue;}else{if(0>=_eP){return __Z;}else{return new F(function(){return _eH(_eP,new T2(1,_eQ,_eR));});}}}},_eT=function(_eU,_eV,_eW){var _eX=E(_eW);if(!_eX._){return __Z;}else{var _eY=E(_eU);if(B(_77(_eX,_eV))!=_eY){return new F(function(){return _eN(_eY,_eV+1|0,_eX.a,_eX.b);});}else{if(0>=_eV){return __Z;}else{return new F(function(){return _eH(_eV,_eX);});}}}},_eZ=function(_f0,_f1,_f2){var _f3=_f1+1|0;if(_f3>0){return new F(function(){return _eB(_f3,B(_eT(_f0,_f3,_f2)));});}else{return new F(function(){return _eT(_f0,_f3,_f2);});}},_f4=function(_f5,_f6,_f7){while(1){var _f8=E(_f5);if(!_f8._){return E(_f7);}else{var _f9=_f8.a,_fa=E(_f6);if(_fa==1){return E(_f9);}else{_f5=_f8.b;_f6=_fa-1|0;_f7=_f9;continue;}}}},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return new T2(0,_10,_10);}else{var _fe=E(_fd.a),_ff=new T(function(){var _fg=B(_fb(_fd.b));return new T2(0,_fg.a,_fg.b);});return new T2(0,new T2(1,_fe.a,new T(function(){return E(E(_ff).a);})),new T2(1,_fe.b,new T(function(){return E(E(_ff).b);})));}},_fh=function(_fi,_fj){while(1){var _fk=E(_fi);if(!_fk._){return (E(_fj)._==0)?true:false;}else{var _fl=E(_fj);if(!_fl._){return false;}else{if(E(_fk.a)!=E(_fl.a)){return false;}else{_fi=_fk.b;_fj=_fl.b;continue;}}}}},_fm=function(_fn,_fo){return (!B(_fh(_fn,_fo)))?true:false;},_fp=new T2(0,_fh,_fm),_fq=0,_fr=new T(function(){return B(_a2("Event.hs:(42,1)-(43,68)|function addEvent"));}),_fs=function(_ft,_fu,_fv,_fw,_fx,_fy,_fz,_fA,_fB,_fC,_fD,_fE,_fF,_fG,_fH,_fI,_fJ,_fK,_fL,_fM,_fN,_fO,_fP,_fQ,_fR,_fS,_fT,_fU,_fV,_fW,_fX){while(1){var _fY=E(_ft);if(!_fY._){return {_:0,a:_fu,b:_fv,c:_fw,d:_fx,e:_fy,f:_fz,g:_fA,h:_fB,i:_fC,j:_fD,k:_fE,l:_fF,m:_fG,n:_fH,o:_fI,p:_fJ,q:_fK,r:_fL,s:_fM,t:_fN,u:_fO,v:_fP,w:_fQ,x:_fR,y:_fS,z:_fT,A:_fU,B:_fV,C:_fW,D:_fX};}else{var _fZ=E(_fY.b);if(!_fZ._){return E(_fr);}else{var _g0=new T2(1,new T2(0,_fY.a,_fZ.a),_fB),_g1=new T2(1,_fq,_fD);_ft=_fZ.b;_fB=_g0;_fD=_g1;continue;}}}},_g2=new T(function(){return B(_a2("Event.hs:(63,1)-(64,57)|function addMemory"));}),_g3=function(_g4,_g5,_g6,_g7,_g8,_g9,_ga,_gb,_gc,_gd,_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_gn,_go,_gp,_gq,_gr,_gs,_gt,_gu,_gv,_gw,_gx,_gy){while(1){var _gz=E(_g4);if(!_gz._){return {_:0,a:_g5,b:_g6,c:_g7,d:_g8,e:_g9,f:_ga,g:_gb,h:_gc,i:_gd,j:_ge,k:_gf,l:_gg,m:_gh,n:_gi,o:_gj,p:_gk,q:_gl,r:_gm,s:_gn,t:_go,u:_gp,v:_gq,w:_gr,x:_gs,y:_gt,z:_gu,A:_gv,B:_gw,C:_gx,D:_gy};}else{var _gA=E(_gz.b);if(!_gA._){return E(_g2);}else{var _gB=new T2(1,new T2(0,_gz.a,_gA.a),_gf);_g4=_gA.b;_gf=_gB;continue;}}}},_gC=function(_gD){var _gE=E(_gD);if(!_gE._){return new T2(0,_10,_10);}else{var _gF=E(_gE.a),_gG=new T(function(){var _gH=B(_gC(_gE.b));return new T2(0,_gH.a,_gH.b);});return new T2(0,new T2(1,_gF.a,new T(function(){return E(E(_gG).a);})),new T2(1,_gF.b,new T(function(){return E(E(_gG).b);})));}},_gI=function(_gJ,_gK,_gL){while(1){var _gM=B((function(_gN,_gO,_gP){var _gQ=E(_gP);if(!_gQ._){return __Z;}else{var _gR=_gQ.b;if(_gO!=E(_gQ.a)){var _gS=_gN+1|0,_gT=_gO;_gJ=_gS;_gK=_gT;_gL=_gR;return __continue;}else{return new T2(1,_gN,new T(function(){return B(_gI(_gN+1|0,_gO,_gR));}));}}})(_gJ,_gK,_gL));if(_gM!=__continue){return _gM;}}},_gU=function(_gV,_gW,_gX){var _gY=E(_gX);if(!_gY._){return __Z;}else{var _gZ=_gY.b,_h0=E(_gW);if(_h0!=E(_gY.a)){return new F(function(){return _gI(_gV+1|0,_h0,_gZ);});}else{return new T2(1,_gV,new T(function(){return B(_gI(_gV+1|0,_h0,_gZ));}));}}},_h1=function(_h2,_h3,_h4,_h5){var _h6=E(_h5);if(!_h6._){return __Z;}else{var _h7=_h6.b;return (!B(_4B(_3M,_h2,_h4)))?new T2(1,_h6.a,new T(function(){return B(_h1(_h2+1|0,_h3,_h4,_h7));})):new T2(1,_h3,new T(function(){return B(_h1(_h2+1|0,_h3,_h4,_h7));}));}},_h8=function(_h9,_ha){var _hb=E(_h9);if(!_hb._){return __Z;}else{var _hc=E(_ha);return (_hc._==0)?__Z:new T2(1,new T2(0,_hb.a,_hc.a),new T(function(){return B(_h8(_hb.b,_hc.b));}));}},_hd=function(_he,_hf,_hg){var _hh=E(_hg);if(!_hh._){return __Z;}else{var _hi=new T(function(){var _hj=B(_gC(_hh.a)),_hk=_hj.a,_hl=new T(function(){return B(_h1(0,_hf,new T(function(){return B(_gU(0,_he,_hk));}),_hj.b));},1);return B(_h8(_hk,_hl));});return new T2(1,_hi,new T(function(){return B(_hd(_he,_hf,_hh.b));}));}},_hm=function(_hn){var _ho=E(_hn);return (_ho._==0)?E(_dJ):E(_ho.a);},_hp=new T(function(){return B(_a2("Event.hs:(37,1)-(39,84)|function changeType"));}),_hq=function(_hr,_hs){while(1){var _ht=E(_hr);if(!_ht._){return (E(_hs)._==0)?true:false;}else{var _hu=E(_hs);if(!_hu._){return false;}else{if(E(_ht.a)!=E(_hu.a)){return false;}else{_hr=_ht.b;_hs=_hu.b;continue;}}}}},_hv=new T(function(){return B(unCStr("Mv"));}),_hw=new T(function(){return B(unCStr("Fr"));}),_hx=new T(function(){return B(unCStr("Ex"));}),_hy=new T(function(){return B(unCStr("DF"));}),_hz=new T(function(){return B(unCStr("DB"));}),_hA=new T(function(){return B(unCStr("Cm"));}),_hB=new T(function(){return B(unCStr("Bl"));}),_hC=new T(function(){return B(_a2("Event.hs:34:16-116|case"));}),_hD=new T(function(){return B(unCStr("Wn"));}),_hE=new T(function(){return B(unCStr("Pn"));}),_hF=function(_hG){return (!B(_hq(_hG,_hB)))?(!B(_hq(_hG,_hA)))?(!B(_hq(_hG,_hz)))?(!B(_hq(_hG,_hy)))?(!B(_hq(_hG,_hx)))?(!B(_hq(_hG,_hw)))?(!B(_hq(_hG,_hv)))?(!B(_hq(_hG,_hE)))?(!B(_hq(_hG,_hD)))?E(_hC):5:4:3:0:2:8:7:6:1;},_hH=function(_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP,_hQ,_hR,_hS,_hT,_hU,_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4,_i5,_i6,_i7,_i8,_i9,_ia,_ib,_ic){while(1){var _id=B((function(_ie,_if,_ig,_ih,_ii,_ij,_ik,_il,_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv,_iw,_ix,_iy,_iz,_iA,_iB,_iC,_iD,_iE,_iF,_iG,_iH,_iI){var _iJ=E(_ie);if(!_iJ._){return {_:0,a:_if,b:_ig,c:_ih,d:_ii,e:_ij,f:_ik,g:_il,h:_im,i:_in,j:_io,k:_ip,l:_iq,m:_ir,n:_is,o:_it,p:_iu,q:_iv,r:_iw,s:_ix,t:_iy,u:_iz,v:_iA,w:_iB,x:_iC,y:_iD,z:_iE,A:_iF,B:_iG,C:_iH,D:_iI};}else{var _iK=E(_iJ.b);if(!_iK._){return E(_hp);}else{var _iL=_if,_iM=_ig,_iN=B(_hd(new T(function(){return B(_hm(_iJ.a));}),new T(function(){return B(_hF(_iK.a));}),_ih)),_iO=_ii,_iP=_ij,_iQ=_ik,_iR=_il,_iS=_im,_iT=_in,_iU=_io,_iV=_ip,_iW=_iq,_iX=_ir,_iY=_is,_iZ=_it,_j0=_iu,_j1=_iv,_j2=_iw,_j3=_ix,_j4=_iy,_j5=_iz,_j6=_iA,_j7=_iB,_j8=_iC,_j9=_iD,_ja=_iE,_jb=_iF,_jc=_iG,_jd=_iH,_je=_iI;_hI=_iK.b;_hJ=_iL;_hK=_iM;_hL=_iN;_hM=_iO;_hN=_iP;_hO=_iQ;_hP=_iR;_hQ=_iS;_hR=_iT;_hS=_iU;_hT=_iV;_hU=_iW;_hV=_iX;_hW=_iY;_hX=_iZ;_hY=_j0;_hZ=_j1;_i0=_j2;_i1=_j3;_i2=_j4;_i3=_j5;_i4=_j6;_i5=_j7;_i6=_j8;_i7=_j9;_i8=_ja;_i9=_jb;_ia=_jc;_ib=_jd;_ic=_je;return __continue;}}})(_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP,_hQ,_hR,_hS,_hT,_hU,_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4,_i5,_i6,_i7,_i8,_i9,_ia,_ib,_ic));if(_id!=__continue){return _id;}}},_jf=function(_jg,_jh,_ji){var _jj=E(_ji);return (_jj._==0)?0:(!B(A3(_4z,_jg,_jh,_jj.a)))?1+B(_jf(_jg,_jh,_jj.b))|0:0;},_jk=function(_jl,_jm){while(1){var _jn=E(_jm);if(!_jn._){return __Z;}else{var _jo=_jn.b,_jp=E(_jl);if(_jp==1){return E(_jo);}else{_jl=_jp-1|0;_jm=_jo;continue;}}}},_jq=function(_jr,_js){var _jt=new T(function(){var _ju=_jr+1|0;if(_ju>0){return B(_jk(_ju,_js));}else{return E(_js);}});if(0>=_jr){return E(_jt);}else{var _jv=function(_jw,_jx){var _jy=E(_jw);if(!_jy._){return E(_jt);}else{var _jz=_jy.a,_jA=E(_jx);return (_jA==1)?new T2(1,_jz,_jt):new T2(1,_jz,new T(function(){return B(_jv(_jy.b,_jA-1|0));}));}};return new F(function(){return _jv(_js,_jr);});}},_jB=function(_jC,_jD){return new F(function(){return _jq(E(_jC),_jD);});},_jE=function(_jF){return E(E(_jF).a);},_jG= -1,_jH=function(_jI,_jJ){var _jK=E(_jJ);return (_jK._==0)?__Z:new T2(1,new T(function(){return B(A1(_jI,_jK.a));}),new T(function(){return B(_jH(_jI,_jK.b));}));},_jL=function(_jM,_jN,_jO,_jP,_jQ,_jR,_jS,_jT,_jU,_jV,_jW,_jX,_jY,_jZ,_k0,_k1,_k2,_k3,_k4,_k5,_k6,_k7,_k8,_k9,_ka,_kb,_kc,_kd,_ke,_kf,_kg){while(1){var _kh=B((function(_ki,_kj,_kk,_kl,_km,_kn,_ko,_kp,_kq,_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_kC,_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM){var _kN=E(_ki);if(!_kN._){return {_:0,a:_kj,b:_kk,c:_kl,d:_km,e:_kn,f:_ko,g:_kp,h:_kq,i:_kr,j:_ks,k:_kt,l:_ku,m:_kv,n:_kw,o:_kx,p:_ky,q:_kz,r:_kA,s:_kB,t:_kC,u:_kD,v:_kE,w:_kF,x:_kG,y:_kH,z:_kI,A:_kJ,B:_kK,C:_kL,D:_kM};}else{var _kO=_kN.a,_kP=B(_jH(_jE,_kq)),_kQ=B(_4B(_fp,_kO,_kP)),_kR=new T(function(){if(!E(_kQ)){return E(_jG);}else{return B(_jf(_fp,_kO,_kP));}});if(!E(_kQ)){var _kS=E(_kq);}else{var _kS=B(_jB(_kR,_kq));}if(!E(_kQ)){var _kT=E(_ks);}else{var _kT=B(_jB(_kR,_ks));}var _kU=_kj,_kV=_kk,_kW=_kl,_kX=_km,_kY=_kn,_kZ=_ko,_l0=_kp,_l1=_kr,_l2=_kt,_l3=_ku,_l4=_kv,_l5=_kw,_l6=_kx,_l7=_ky,_l8=_kz,_l9=_kA,_la=_kB,_lb=_kC,_lc=_kD,_ld=_kE,_le=_kF,_lf=_kG,_lg=_kH,_lh=_kI,_li=_kJ,_lj=_kK,_lk=_kL,_ll=_kM;_jM=_kN.b;_jN=_kU;_jO=_kV;_jP=_kW;_jQ=_kX;_jR=_kY;_jS=_kZ;_jT=_l0;_jU=_kS;_jV=_l1;_jW=_kT;_jX=_l2;_jY=_l3;_jZ=_l4;_k0=_l5;_k1=_l6;_k2=_l7;_k3=_l8;_k4=_l9;_k5=_la;_k6=_lb;_k7=_lc;_k8=_ld;_k9=_le;_ka=_lf;_kb=_lg;_kc=_lh;_kd=_li;_ke=_lj;_kf=_lk;_kg=_ll;return __continue;}})(_jM,_jN,_jO,_jP,_jQ,_jR,_jS,_jT,_jU,_jV,_jW,_jX,_jY,_jZ,_k0,_k1,_k2,_k3,_k4,_k5,_k6,_k7,_k8,_k9,_ka,_kb,_kc,_kd,_ke,_kf,_kg));if(_kh!=__continue){return _kh;}}},_lm=function(_ln){var _lo=E(_ln);if(!_lo._){return new T2(0,_10,_10);}else{var _lp=E(_lo.a),_lq=new T(function(){var _lr=B(_lm(_lo.b));return new T2(0,_lr.a,_lr.b);});return new T2(0,new T2(1,_lp.a,new T(function(){return E(E(_lq).a);})),new T2(1,_lp.b,new T(function(){return E(E(_lq).b);})));}},_ls=true,_lt=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_lu=function(_lv){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9R(_lv,_lt));})),_9o);});},_lw=function(_lx){return new F(function(){return _lu("Event.hs:77:28-52|(c : d : _)");});},_ly=new T(function(){return B(_lw(_));}),_lz=function(_lA,_lB,_lC){var _lD=E(_lC);if(!_lD._){return new T2(0,new T2(1,_lB,_10),_10);}else{var _lE=E(_lB),_lF=new T(function(){var _lG=B(_lz(_lA,_lD.a,_lD.b));return new T2(0,_lG.a,_lG.b);});return (_lA!=_lE)?new T2(0,new T2(1,_lE,new T(function(){return E(E(_lF).a);})),new T(function(){return E(E(_lF).b);})):new T2(0,_10,new T2(1,new T(function(){return E(E(_lF).a);}),new T(function(){return E(E(_lF).b);})));}},_lH=function(_lI,_lJ,_lK,_lL,_lM,_lN,_lO,_lP,_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_lX,_lY,_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_m6,_m7,_m8,_m9,_ma,_mb,_mc){while(1){var _md=B((function(_me,_mf,_mg,_mh,_mi,_mj,_mk,_ml,_mm,_mn,_mo,_mp,_mq,_mr,_ms,_mt,_mu,_mv,_mw,_mx,_my,_mz,_mA,_mB,_mC,_mD,_mE,_mF,_mG,_mH,_mI){var _mJ=E(_me);if(!_mJ._){return {_:0,a:E(_mf),b:E(_mg),c:E(_mh),d:_mi,e:_mj,f:_mk,g:E(_ml),h:E(_mm),i:E(_mn),j:E(_mo),k:E(_mp),l:E(_mq),m:_mr,n:_ms,o:_mt,p:_mu,q:_mv,r:E(_mw),s:_mx,t:E(_my),u:E(_mz),v:E(_mA),w:E(_mB),x:E(_ls),y:E(_mD),z:E(_mE),A:E(_mF),B:E(_ls),C:E(_mH),D:_mI};}else{var _mK=new T(function(){var _mL=E(_mJ.a);if(!_mL._){return E(_ly);}else{var _mM=E(_mL.b);if(!_mM._){return E(_ly);}else{var _mN=_mM.a,_mO=_mM.b,_mP=E(_mL.a);if(E(_mP)==44){return new T2(0,_10,new T(function(){return E(B(_lz(44,_mN,_mO)).a);}));}else{var _mQ=B(_lz(44,_mN,_mO)),_mR=E(_mQ.b);if(!_mR._){return E(_ly);}else{return new T2(0,new T2(1,_mP,_mQ.a),_mR.a);}}}}}),_mS=_mf,_mT=_mg,_mU=_mh,_mV=_mi,_mW=_mj,_mX=_mk,_mY=_ml,_mZ=_mm,_n0=_mn,_n1=_mo,_n2=_mp,_n3=_mq,_n4=_mr,_n5=_ms,_n6=_mt,_n7=_mu,_n8=_mv,_n9=B(_y(_mw,new T2(1,new T2(0,new T(function(){return E(E(_mK).a);}),new T(function(){return E(E(_mK).b);})),_10))),_na=_mx,_nb=_my,_nc=_mz,_nd=_mA,_ne=_mB,_nf=_mC,_ng=_mD,_nh=_mE,_ni=_mF,_nj=_mG,_nk=_mH,_nl=_mI;_lI=_mJ.b;_lJ=_mS;_lK=_mT;_lL=_mU;_lM=_mV;_lN=_mW;_lO=_mX;_lP=_mY;_lQ=_mZ;_lR=_n0;_lS=_n1;_lT=_n2;_lU=_n3;_lV=_n4;_lW=_n5;_lX=_n6;_lY=_n7;_lZ=_n8;_m0=_n9;_m1=_na;_m2=_nb;_m3=_nc;_m4=_nd;_m5=_ne;_m6=_nf;_m7=_ng;_m8=_nh;_m9=_ni;_ma=_nj;_mb=_nk;_mc=_nl;return __continue;}})(_lI,_lJ,_lK,_lL,_lM,_lN,_lO,_lP,_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_lX,_lY,_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_m6,_m7,_m8,_m9,_ma,_mb,_mc));if(_md!=__continue){return _md;}}},_nm=function(_nn,_no){while(1){var _np=E(_no);if(!_np._){return __Z;}else{var _nq=_np.b,_nr=E(_nn);if(_nr==1){return E(_nq);}else{_nn=_nr-1|0;_no=_nq;continue;}}}},_ns=function(_nt,_nu){while(1){var _nv=E(_nu);if(!_nv._){return __Z;}else{var _nw=_nv.b,_nx=E(_nt);if(_nx==1){return E(_nw);}else{_nt=_nx-1|0;_nu=_nw;continue;}}}},_ny=function(_nz,_nA,_nB,_nC,_nD){var _nE=new T(function(){var _nF=E(_nz),_nG=new T(function(){return B(_77(_nD,_nA));}),_nH=new T2(1,new T2(0,_nB,_nC),new T(function(){var _nI=_nF+1|0;if(_nI>0){return B(_ns(_nI,_nG));}else{return E(_nG);}}));if(0>=_nF){return E(_nH);}else{var _nJ=function(_nK,_nL){var _nM=E(_nK);if(!_nM._){return E(_nH);}else{var _nN=_nM.a,_nO=E(_nL);return (_nO==1)?new T2(1,_nN,_nH):new T2(1,_nN,new T(function(){return B(_nJ(_nM.b,_nO-1|0));}));}};return B(_nJ(_nG,_nF));}}),_nP=new T2(1,_nE,new T(function(){var _nQ=_nA+1|0;if(_nQ>0){return B(_nm(_nQ,_nD));}else{return E(_nD);}}));if(0>=_nA){return E(_nP);}else{var _nR=function(_nS,_nT){var _nU=E(_nS);if(!_nU._){return E(_nP);}else{var _nV=_nU.a,_nW=E(_nT);return (_nW==1)?new T2(1,_nV,_nP):new T2(1,_nV,new T(function(){return B(_nR(_nU.b,_nW-1|0));}));}};return new F(function(){return _nR(_nD,_nA);});}},_nX=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_nY=new T(function(){return B(err(_nX));}),_nZ=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_o0=new T(function(){return B(err(_nZ));}),_o1=function(_o2){return new F(function(){return _lu("Event.hs:27:27-53|(x\' : y\' : _)");});},_o3=new T(function(){return B(_o1(_));}),_o4=function(_o5){return new F(function(){return _lu("Event.hs:28:27-55|(chs : tps : _)");});},_o6=new T(function(){return B(_o4(_));}),_o7=new T(function(){return B(_a2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_o8=function(_o9,_oa){while(1){var _ob=B((function(_oc,_od){var _oe=E(_oc);switch(_oe._){case 0:var _of=E(_od);if(!_of._){return __Z;}else{_o9=B(A1(_oe.a,_of.a));_oa=_of.b;return __continue;}break;case 1:var _og=B(A1(_oe.a,_od)),_oh=_od;_o9=_og;_oa=_oh;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_oe.a,_od),new T(function(){return B(_o8(_oe.b,_od));}));default:return E(_oe.a);}})(_o9,_oa));if(_ob!=__continue){return _ob;}}},_oi=function(_oj,_ok){var _ol=function(_om){var _on=E(_ok);if(_on._==3){return new T2(3,_on.a,new T(function(){return B(_oi(_oj,_on.b));}));}else{var _oo=E(_oj);if(_oo._==2){return E(_on);}else{var _op=E(_on);if(_op._==2){return E(_oo);}else{var _oq=function(_or){var _os=E(_op);if(_os._==4){var _ot=function(_ou){return new T1(4,new T(function(){return B(_y(B(_o8(_oo,_ou)),_os.a));}));};return new T1(1,_ot);}else{var _ov=E(_oo);if(_ov._==1){var _ow=_ov.a,_ox=E(_os);if(!_ox._){return new T1(1,function(_oy){return new F(function(){return _oi(B(A1(_ow,_oy)),_ox);});});}else{var _oz=function(_oA){return new F(function(){return _oi(B(A1(_ow,_oA)),new T(function(){return B(A1(_ox.a,_oA));}));});};return new T1(1,_oz);}}else{var _oB=E(_os);if(!_oB._){return E(_o7);}else{var _oC=function(_oD){return new F(function(){return _oi(_ov,new T(function(){return B(A1(_oB.a,_oD));}));});};return new T1(1,_oC);}}}},_oE=E(_oo);switch(_oE._){case 1:var _oF=E(_op);if(_oF._==4){var _oG=function(_oH){return new T1(4,new T(function(){return B(_y(B(_o8(B(A1(_oE.a,_oH)),_oH)),_oF.a));}));};return new T1(1,_oG);}else{return new F(function(){return _oq(_);});}break;case 4:var _oI=_oE.a,_oJ=E(_op);switch(_oJ._){case 0:var _oK=function(_oL){var _oM=new T(function(){return B(_y(_oI,new T(function(){return B(_o8(_oJ,_oL));},1)));});return new T1(4,_oM);};return new T1(1,_oK);case 1:var _oN=function(_oO){var _oP=new T(function(){return B(_y(_oI,new T(function(){return B(_o8(B(A1(_oJ.a,_oO)),_oO));},1)));});return new T1(4,_oP);};return new T1(1,_oN);default:return new T1(4,new T(function(){return B(_y(_oI,_oJ.a));}));}break;default:return new F(function(){return _oq(_);});}}}}},_oQ=E(_oj);switch(_oQ._){case 0:var _oR=E(_ok);if(!_oR._){var _oS=function(_oT){return new F(function(){return _oi(B(A1(_oQ.a,_oT)),new T(function(){return B(A1(_oR.a,_oT));}));});};return new T1(0,_oS);}else{return new F(function(){return _ol(_);});}break;case 3:return new T2(3,_oQ.a,new T(function(){return B(_oi(_oQ.b,_ok));}));default:return new F(function(){return _ol(_);});}},_oU=new T(function(){return B(unCStr("("));}),_oV=new T(function(){return B(unCStr(")"));}),_oW=function(_oX,_oY){var _oZ=E(_oX);switch(_oZ._){case 0:return new T1(0,function(_p0){return new F(function(){return _oW(B(A1(_oZ.a,_p0)),_oY);});});case 1:return new T1(1,function(_p1){return new F(function(){return _oW(B(A1(_oZ.a,_p1)),_oY);});});case 2:return new T0(2);case 3:return new F(function(){return _oi(B(A1(_oY,_oZ.a)),new T(function(){return B(_oW(_oZ.b,_oY));}));});break;default:var _p2=function(_p3){var _p4=E(_p3);if(!_p4._){return __Z;}else{var _p5=E(_p4.a);return new F(function(){return _y(B(_o8(B(A1(_oY,_p5.a)),_p5.b)),new T(function(){return B(_p2(_p4.b));},1));});}},_p6=B(_p2(_oZ.a));return (_p6._==0)?new T0(2):new T1(4,_p6);}},_p7=new T0(2),_p8=function(_p9){return new T2(3,_p9,_p7);},_pa=function(_pb,_pc){var _pd=E(_pb);if(!_pd){return new F(function(){return A1(_pc,_7f);});}else{var _pe=new T(function(){return B(_pa(_pd-1|0,_pc));});return new T1(0,function(_pf){return E(_pe);});}},_pg=function(_ph,_pi,_pj){var _pk=new T(function(){return B(A1(_ph,_p8));}),_pl=function(_pm,_pn,_po,_pp){while(1){var _pq=B((function(_pr,_ps,_pt,_pu){var _pv=E(_pr);switch(_pv._){case 0:var _pw=E(_ps);if(!_pw._){return new F(function(){return A1(_pi,_pu);});}else{var _px=_pt+1|0,_py=_pu;_pm=B(A1(_pv.a,_pw.a));_pn=_pw.b;_po=_px;_pp=_py;return __continue;}break;case 1:var _pz=B(A1(_pv.a,_ps)),_pA=_ps,_px=_pt,_py=_pu;_pm=_pz;_pn=_pA;_po=_px;_pp=_py;return __continue;case 2:return new F(function(){return A1(_pi,_pu);});break;case 3:var _pB=new T(function(){return B(_oW(_pv,_pu));});return new F(function(){return _pa(_pt,function(_pC){return E(_pB);});});break;default:return new F(function(){return _oW(_pv,_pu);});}})(_pm,_pn,_po,_pp));if(_pq!=__continue){return _pq;}}};return function(_pD){return new F(function(){return _pl(_pk,_pD,0,_pj);});};},_pE=function(_pF){return new F(function(){return A1(_pF,_10);});},_pG=function(_pH,_pI){var _pJ=function(_pK){var _pL=E(_pK);if(!_pL._){return E(_pE);}else{var _pM=_pL.a;if(!B(A1(_pH,_pM))){return E(_pE);}else{var _pN=new T(function(){return B(_pJ(_pL.b));}),_pO=function(_pP){var _pQ=new T(function(){return B(A1(_pN,function(_pR){return new F(function(){return A1(_pP,new T2(1,_pM,_pR));});}));});return new T1(0,function(_pS){return E(_pQ);});};return E(_pO);}}};return function(_pT){return new F(function(){return A2(_pJ,_pT,_pI);});};},_pU=new T0(6),_pV=new T(function(){return B(unCStr("valDig: Bad base"));}),_pW=new T(function(){return B(err(_pV));}),_pX=function(_pY,_pZ){var _q0=function(_q1,_q2){var _q3=E(_q1);if(!_q3._){var _q4=new T(function(){return B(A1(_q2,_10));});return function(_q5){return new F(function(){return A1(_q5,_q4);});};}else{var _q6=E(_q3.a),_q7=function(_q8){var _q9=new T(function(){return B(_q0(_q3.b,function(_qa){return new F(function(){return A1(_q2,new T2(1,_q8,_qa));});}));}),_qb=function(_qc){var _qd=new T(function(){return B(A1(_q9,_qc));});return new T1(0,function(_qe){return E(_qd);});};return E(_qb);};switch(E(_pY)){case 8:if(48>_q6){var _qf=new T(function(){return B(A1(_q2,_10));});return function(_qg){return new F(function(){return A1(_qg,_qf);});};}else{if(_q6>55){var _qh=new T(function(){return B(A1(_q2,_10));});return function(_qi){return new F(function(){return A1(_qi,_qh);});};}else{return new F(function(){return _q7(_q6-48|0);});}}break;case 10:if(48>_q6){var _qj=new T(function(){return B(A1(_q2,_10));});return function(_qk){return new F(function(){return A1(_qk,_qj);});};}else{if(_q6>57){var _ql=new T(function(){return B(A1(_q2,_10));});return function(_qm){return new F(function(){return A1(_qm,_ql);});};}else{return new F(function(){return _q7(_q6-48|0);});}}break;case 16:if(48>_q6){if(97>_q6){if(65>_q6){var _qn=new T(function(){return B(A1(_q2,_10));});return function(_qo){return new F(function(){return A1(_qo,_qn);});};}else{if(_q6>70){var _qp=new T(function(){return B(A1(_q2,_10));});return function(_qq){return new F(function(){return A1(_qq,_qp);});};}else{return new F(function(){return _q7((_q6-65|0)+10|0);});}}}else{if(_q6>102){if(65>_q6){var _qr=new T(function(){return B(A1(_q2,_10));});return function(_qs){return new F(function(){return A1(_qs,_qr);});};}else{if(_q6>70){var _qt=new T(function(){return B(A1(_q2,_10));});return function(_qu){return new F(function(){return A1(_qu,_qt);});};}else{return new F(function(){return _q7((_q6-65|0)+10|0);});}}}else{return new F(function(){return _q7((_q6-97|0)+10|0);});}}}else{if(_q6>57){if(97>_q6){if(65>_q6){var _qv=new T(function(){return B(A1(_q2,_10));});return function(_qw){return new F(function(){return A1(_qw,_qv);});};}else{if(_q6>70){var _qx=new T(function(){return B(A1(_q2,_10));});return function(_qy){return new F(function(){return A1(_qy,_qx);});};}else{return new F(function(){return _q7((_q6-65|0)+10|0);});}}}else{if(_q6>102){if(65>_q6){var _qz=new T(function(){return B(A1(_q2,_10));});return function(_qA){return new F(function(){return A1(_qA,_qz);});};}else{if(_q6>70){var _qB=new T(function(){return B(A1(_q2,_10));});return function(_qC){return new F(function(){return A1(_qC,_qB);});};}else{return new F(function(){return _q7((_q6-65|0)+10|0);});}}}else{return new F(function(){return _q7((_q6-97|0)+10|0);});}}}else{return new F(function(){return _q7(_q6-48|0);});}}break;default:return E(_pW);}}},_qD=function(_qE){var _qF=E(_qE);if(!_qF._){return new T0(2);}else{return new F(function(){return A1(_pZ,_qF);});}};return function(_qG){return new F(function(){return A3(_q0,_qG,_5V,_qD);});};},_qH=16,_qI=8,_qJ=function(_qK){var _qL=function(_qM){return new F(function(){return A1(_qK,new T1(5,new T2(0,_qI,_qM)));});},_qN=function(_qO){return new F(function(){return A1(_qK,new T1(5,new T2(0,_qH,_qO)));});},_qP=function(_qQ){switch(E(_qQ)){case 79:return new T1(1,B(_pX(_qI,_qL)));case 88:return new T1(1,B(_pX(_qH,_qN)));case 111:return new T1(1,B(_pX(_qI,_qL)));case 120:return new T1(1,B(_pX(_qH,_qN)));default:return new T0(2);}};return function(_qR){return (E(_qR)==48)?E(new T1(0,_qP)):new T0(2);};},_qS=function(_qT){return new T1(0,B(_qJ(_qT)));},_qU=function(_qV){return new F(function(){return A1(_qV,_0);});},_qW=function(_qX){return new F(function(){return A1(_qX,_0);});},_qY=10,_qZ=new T1(0,10),_r0=function(_r1){return new T1(0,_r1);},_r2=function(_r3){return new F(function(){return _r0(E(_r3));});},_r4=new T(function(){return B(unCStr("this should not happen"));}),_r5=new T(function(){return B(err(_r4));}),_r6=function(_r7,_r8){while(1){var _r9=E(_r7);if(!_r9._){var _ra=_r9.a,_rb=E(_r8);if(!_rb._){var _rc=_rb.a;if(!(imul(_ra,_rc)|0)){return new T1(0,imul(_ra,_rc)|0);}else{_r7=new T1(1,I_fromInt(_ra));_r8=new T1(1,I_fromInt(_rc));continue;}}else{_r7=new T1(1,I_fromInt(_ra));_r8=_rb;continue;}}else{var _rd=E(_r8);if(!_rd._){_r7=_r9;_r8=new T1(1,I_fromInt(_rd.a));continue;}else{return new T1(1,I_mul(_r9.a,_rd.a));}}}},_re=function(_rf,_rg){var _rh=E(_rg);if(!_rh._){return __Z;}else{var _ri=E(_rh.b);return (_ri._==0)?E(_r5):new T2(1,B(_8q(B(_r6(_rh.a,_rf)),_ri.a)),new T(function(){return B(_re(_rf,_ri.b));}));}},_rj=new T1(0,0),_rk=function(_rl,_rm,_rn){while(1){var _ro=B((function(_rp,_rq,_rr){var _rs=E(_rr);if(!_rs._){return E(_rj);}else{if(!E(_rs.b)._){return E(_rs.a);}else{var _rt=E(_rq);if(_rt<=40){var _ru=function(_rv,_rw){while(1){var _rx=E(_rw);if(!_rx._){return E(_rv);}else{var _ry=B(_8q(B(_r6(_rv,_rp)),_rx.a));_rv=_ry;_rw=_rx.b;continue;}}};return new F(function(){return _ru(_rj,_rs);});}else{var _rz=B(_r6(_rp,_rp));if(!(_rt%2)){var _rA=B(_re(_rp,_rs));_rl=_rz;_rm=quot(_rt+1|0,2);_rn=_rA;return __continue;}else{var _rA=B(_re(_rp,new T2(1,_rj,_rs)));_rl=_rz;_rm=quot(_rt+1|0,2);_rn=_rA;return __continue;}}}}})(_rl,_rm,_rn));if(_ro!=__continue){return _ro;}}},_rB=function(_rC,_rD){return new F(function(){return _rk(_rC,new T(function(){return B(_7a(_rD,0));},1),B(_jH(_r2,_rD)));});},_rE=function(_rF){var _rG=new T(function(){var _rH=new T(function(){var _rI=function(_rJ){return new F(function(){return A1(_rF,new T1(1,new T(function(){return B(_rB(_qZ,_rJ));})));});};return new T1(1,B(_pX(_qY,_rI)));}),_rK=function(_rL){if(E(_rL)==43){var _rM=function(_rN){return new F(function(){return A1(_rF,new T1(1,new T(function(){return B(_rB(_qZ,_rN));})));});};return new T1(1,B(_pX(_qY,_rM)));}else{return new T0(2);}},_rO=function(_rP){if(E(_rP)==45){var _rQ=function(_rR){return new F(function(){return A1(_rF,new T1(1,new T(function(){return B(_bo(B(_rB(_qZ,_rR))));})));});};return new T1(1,B(_pX(_qY,_rQ)));}else{return new T0(2);}};return B(_oi(B(_oi(new T1(0,_rO),new T1(0,_rK))),_rH));});return new F(function(){return _oi(new T1(0,function(_rS){return (E(_rS)==101)?E(_rG):new T0(2);}),new T1(0,function(_rT){return (E(_rT)==69)?E(_rG):new T0(2);}));});},_rU=function(_rV){var _rW=function(_rX){return new F(function(){return A1(_rV,new T1(1,_rX));});};return function(_rY){return (E(_rY)==46)?new T1(1,B(_pX(_qY,_rW))):new T0(2);};},_rZ=function(_s0){return new T1(0,B(_rU(_s0)));},_s1=function(_s2){var _s3=function(_s4){var _s5=function(_s6){return new T1(1,B(_pg(_rE,_qU,function(_s7){return new F(function(){return A1(_s2,new T1(5,new T3(1,_s4,_s6,_s7)));});})));};return new T1(1,B(_pg(_rZ,_qW,_s5)));};return new F(function(){return _pX(_qY,_s3);});},_s8=function(_s9){return new T1(1,B(_s1(_s9)));},_sa=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_sb=function(_sc){return new F(function(){return _4B(_6f,_sc,_sa);});},_sd=false,_se=function(_sf){var _sg=new T(function(){return B(A1(_sf,_qI));}),_sh=new T(function(){return B(A1(_sf,_qH));});return function(_si){switch(E(_si)){case 79:return E(_sg);case 88:return E(_sh);case 111:return E(_sg);case 120:return E(_sh);default:return new T0(2);}};},_sj=function(_sk){return new T1(0,B(_se(_sk)));},_sl=function(_sm){return new F(function(){return A1(_sm,_qY);});},_sn=function(_so){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_I(9,_so,_10));}))));});},_sp=function(_sq){return new T0(2);},_sr=function(_ss){var _st=E(_ss);if(!_st._){return E(_sp);}else{var _su=_st.a,_sv=E(_st.b);if(!_sv._){return E(_su);}else{var _sw=new T(function(){return B(_sr(_sv));}),_sx=function(_sy){return new F(function(){return _oi(B(A1(_su,_sy)),new T(function(){return B(A1(_sw,_sy));}));});};return E(_sx);}}},_sz=function(_sA,_sB){var _sC=function(_sD,_sE,_sF){var _sG=E(_sD);if(!_sG._){return new F(function(){return A1(_sF,_sA);});}else{var _sH=E(_sE);if(!_sH._){return new T0(2);}else{if(E(_sG.a)!=E(_sH.a)){return new T0(2);}else{var _sI=new T(function(){return B(_sC(_sG.b,_sH.b,_sF));});return new T1(0,function(_sJ){return E(_sI);});}}}};return function(_sK){return new F(function(){return _sC(_sA,_sK,_sB);});};},_sL=new T(function(){return B(unCStr("SO"));}),_sM=14,_sN=function(_sO){var _sP=new T(function(){return B(A1(_sO,_sM));});return new T1(1,B(_sz(_sL,function(_sQ){return E(_sP);})));},_sR=new T(function(){return B(unCStr("SOH"));}),_sS=1,_sT=function(_sU){var _sV=new T(function(){return B(A1(_sU,_sS));});return new T1(1,B(_sz(_sR,function(_sW){return E(_sV);})));},_sX=function(_sY){return new T1(1,B(_pg(_sT,_sN,_sY)));},_sZ=new T(function(){return B(unCStr("NUL"));}),_t0=0,_t1=function(_t2){var _t3=new T(function(){return B(A1(_t2,_t0));});return new T1(1,B(_sz(_sZ,function(_t4){return E(_t3);})));},_t5=new T(function(){return B(unCStr("STX"));}),_t6=2,_t7=function(_t8){var _t9=new T(function(){return B(A1(_t8,_t6));});return new T1(1,B(_sz(_t5,function(_ta){return E(_t9);})));},_tb=new T(function(){return B(unCStr("ETX"));}),_tc=3,_td=function(_te){var _tf=new T(function(){return B(A1(_te,_tc));});return new T1(1,B(_sz(_tb,function(_tg){return E(_tf);})));},_th=new T(function(){return B(unCStr("EOT"));}),_ti=4,_tj=function(_tk){var _tl=new T(function(){return B(A1(_tk,_ti));});return new T1(1,B(_sz(_th,function(_tm){return E(_tl);})));},_tn=new T(function(){return B(unCStr("ENQ"));}),_to=5,_tp=function(_tq){var _tr=new T(function(){return B(A1(_tq,_to));});return new T1(1,B(_sz(_tn,function(_ts){return E(_tr);})));},_tt=new T(function(){return B(unCStr("ACK"));}),_tu=6,_tv=function(_tw){var _tx=new T(function(){return B(A1(_tw,_tu));});return new T1(1,B(_sz(_tt,function(_ty){return E(_tx);})));},_tz=new T(function(){return B(unCStr("BEL"));}),_tA=7,_tB=function(_tC){var _tD=new T(function(){return B(A1(_tC,_tA));});return new T1(1,B(_sz(_tz,function(_tE){return E(_tD);})));},_tF=new T(function(){return B(unCStr("BS"));}),_tG=8,_tH=function(_tI){var _tJ=new T(function(){return B(A1(_tI,_tG));});return new T1(1,B(_sz(_tF,function(_tK){return E(_tJ);})));},_tL=new T(function(){return B(unCStr("HT"));}),_tM=9,_tN=function(_tO){var _tP=new T(function(){return B(A1(_tO,_tM));});return new T1(1,B(_sz(_tL,function(_tQ){return E(_tP);})));},_tR=new T(function(){return B(unCStr("LF"));}),_tS=10,_tT=function(_tU){var _tV=new T(function(){return B(A1(_tU,_tS));});return new T1(1,B(_sz(_tR,function(_tW){return E(_tV);})));},_tX=new T(function(){return B(unCStr("VT"));}),_tY=11,_tZ=function(_u0){var _u1=new T(function(){return B(A1(_u0,_tY));});return new T1(1,B(_sz(_tX,function(_u2){return E(_u1);})));},_u3=new T(function(){return B(unCStr("FF"));}),_u4=12,_u5=function(_u6){var _u7=new T(function(){return B(A1(_u6,_u4));});return new T1(1,B(_sz(_u3,function(_u8){return E(_u7);})));},_u9=new T(function(){return B(unCStr("CR"));}),_ua=13,_ub=function(_uc){var _ud=new T(function(){return B(A1(_uc,_ua));});return new T1(1,B(_sz(_u9,function(_ue){return E(_ud);})));},_uf=new T(function(){return B(unCStr("SI"));}),_ug=15,_uh=function(_ui){var _uj=new T(function(){return B(A1(_ui,_ug));});return new T1(1,B(_sz(_uf,function(_uk){return E(_uj);})));},_ul=new T(function(){return B(unCStr("DLE"));}),_um=16,_un=function(_uo){var _up=new T(function(){return B(A1(_uo,_um));});return new T1(1,B(_sz(_ul,function(_uq){return E(_up);})));},_ur=new T(function(){return B(unCStr("DC1"));}),_us=17,_ut=function(_uu){var _uv=new T(function(){return B(A1(_uu,_us));});return new T1(1,B(_sz(_ur,function(_uw){return E(_uv);})));},_ux=new T(function(){return B(unCStr("DC2"));}),_uy=18,_uz=function(_uA){var _uB=new T(function(){return B(A1(_uA,_uy));});return new T1(1,B(_sz(_ux,function(_uC){return E(_uB);})));},_uD=new T(function(){return B(unCStr("DC3"));}),_uE=19,_uF=function(_uG){var _uH=new T(function(){return B(A1(_uG,_uE));});return new T1(1,B(_sz(_uD,function(_uI){return E(_uH);})));},_uJ=new T(function(){return B(unCStr("DC4"));}),_uK=20,_uL=function(_uM){var _uN=new T(function(){return B(A1(_uM,_uK));});return new T1(1,B(_sz(_uJ,function(_uO){return E(_uN);})));},_uP=new T(function(){return B(unCStr("NAK"));}),_uQ=21,_uR=function(_uS){var _uT=new T(function(){return B(A1(_uS,_uQ));});return new T1(1,B(_sz(_uP,function(_uU){return E(_uT);})));},_uV=new T(function(){return B(unCStr("SYN"));}),_uW=22,_uX=function(_uY){var _uZ=new T(function(){return B(A1(_uY,_uW));});return new T1(1,B(_sz(_uV,function(_v0){return E(_uZ);})));},_v1=new T(function(){return B(unCStr("ETB"));}),_v2=23,_v3=function(_v4){var _v5=new T(function(){return B(A1(_v4,_v2));});return new T1(1,B(_sz(_v1,function(_v6){return E(_v5);})));},_v7=new T(function(){return B(unCStr("CAN"));}),_v8=24,_v9=function(_va){var _vb=new T(function(){return B(A1(_va,_v8));});return new T1(1,B(_sz(_v7,function(_vc){return E(_vb);})));},_vd=new T(function(){return B(unCStr("EM"));}),_ve=25,_vf=function(_vg){var _vh=new T(function(){return B(A1(_vg,_ve));});return new T1(1,B(_sz(_vd,function(_vi){return E(_vh);})));},_vj=new T(function(){return B(unCStr("SUB"));}),_vk=26,_vl=function(_vm){var _vn=new T(function(){return B(A1(_vm,_vk));});return new T1(1,B(_sz(_vj,function(_vo){return E(_vn);})));},_vp=new T(function(){return B(unCStr("ESC"));}),_vq=27,_vr=function(_vs){var _vt=new T(function(){return B(A1(_vs,_vq));});return new T1(1,B(_sz(_vp,function(_vu){return E(_vt);})));},_vv=new T(function(){return B(unCStr("FS"));}),_vw=28,_vx=function(_vy){var _vz=new T(function(){return B(A1(_vy,_vw));});return new T1(1,B(_sz(_vv,function(_vA){return E(_vz);})));},_vB=new T(function(){return B(unCStr("GS"));}),_vC=29,_vD=function(_vE){var _vF=new T(function(){return B(A1(_vE,_vC));});return new T1(1,B(_sz(_vB,function(_vG){return E(_vF);})));},_vH=new T(function(){return B(unCStr("RS"));}),_vI=30,_vJ=function(_vK){var _vL=new T(function(){return B(A1(_vK,_vI));});return new T1(1,B(_sz(_vH,function(_vM){return E(_vL);})));},_vN=new T(function(){return B(unCStr("US"));}),_vO=31,_vP=function(_vQ){var _vR=new T(function(){return B(A1(_vQ,_vO));});return new T1(1,B(_sz(_vN,function(_vS){return E(_vR);})));},_vT=new T(function(){return B(unCStr("SP"));}),_vU=32,_vV=function(_vW){var _vX=new T(function(){return B(A1(_vW,_vU));});return new T1(1,B(_sz(_vT,function(_vY){return E(_vX);})));},_vZ=new T(function(){return B(unCStr("DEL"));}),_w0=127,_w1=function(_w2){var _w3=new T(function(){return B(A1(_w2,_w0));});return new T1(1,B(_sz(_vZ,function(_w4){return E(_w3);})));},_w5=new T2(1,_w1,_10),_w6=new T2(1,_vV,_w5),_w7=new T2(1,_vP,_w6),_w8=new T2(1,_vJ,_w7),_w9=new T2(1,_vD,_w8),_wa=new T2(1,_vx,_w9),_wb=new T2(1,_vr,_wa),_wc=new T2(1,_vl,_wb),_wd=new T2(1,_vf,_wc),_we=new T2(1,_v9,_wd),_wf=new T2(1,_v3,_we),_wg=new T2(1,_uX,_wf),_wh=new T2(1,_uR,_wg),_wi=new T2(1,_uL,_wh),_wj=new T2(1,_uF,_wi),_wk=new T2(1,_uz,_wj),_wl=new T2(1,_ut,_wk),_wm=new T2(1,_un,_wl),_wn=new T2(1,_uh,_wm),_wo=new T2(1,_ub,_wn),_wp=new T2(1,_u5,_wo),_wq=new T2(1,_tZ,_wp),_wr=new T2(1,_tT,_wq),_ws=new T2(1,_tN,_wr),_wt=new T2(1,_tH,_ws),_wu=new T2(1,_tB,_wt),_wv=new T2(1,_tv,_wu),_ww=new T2(1,_tp,_wv),_wx=new T2(1,_tj,_ww),_wy=new T2(1,_td,_wx),_wz=new T2(1,_t7,_wy),_wA=new T2(1,_t1,_wz),_wB=new T2(1,_sX,_wA),_wC=new T(function(){return B(_sr(_wB));}),_wD=34,_wE=new T1(0,1114111),_wF=92,_wG=39,_wH=function(_wI){var _wJ=new T(function(){return B(A1(_wI,_tA));}),_wK=new T(function(){return B(A1(_wI,_tG));}),_wL=new T(function(){return B(A1(_wI,_tM));}),_wM=new T(function(){return B(A1(_wI,_tS));}),_wN=new T(function(){return B(A1(_wI,_tY));}),_wO=new T(function(){return B(A1(_wI,_u4));}),_wP=new T(function(){return B(A1(_wI,_ua));}),_wQ=new T(function(){return B(A1(_wI,_wF));}),_wR=new T(function(){return B(A1(_wI,_wG));}),_wS=new T(function(){return B(A1(_wI,_wD));}),_wT=new T(function(){var _wU=function(_wV){var _wW=new T(function(){return B(_r0(E(_wV)));}),_wX=function(_wY){var _wZ=B(_rB(_wW,_wY));if(!B(_au(_wZ,_wE))){return new T0(2);}else{return new F(function(){return A1(_wI,new T(function(){var _x0=B(_8n(_wZ));if(_x0>>>0>1114111){return B(_sn(_x0));}else{return _x0;}}));});}};return new T1(1,B(_pX(_wV,_wX)));},_x1=new T(function(){var _x2=new T(function(){return B(A1(_wI,_vO));}),_x3=new T(function(){return B(A1(_wI,_vI));}),_x4=new T(function(){return B(A1(_wI,_vC));}),_x5=new T(function(){return B(A1(_wI,_vw));}),_x6=new T(function(){return B(A1(_wI,_vq));}),_x7=new T(function(){return B(A1(_wI,_vk));}),_x8=new T(function(){return B(A1(_wI,_ve));}),_x9=new T(function(){return B(A1(_wI,_v8));}),_xa=new T(function(){return B(A1(_wI,_v2));}),_xb=new T(function(){return B(A1(_wI,_uW));}),_xc=new T(function(){return B(A1(_wI,_uQ));}),_xd=new T(function(){return B(A1(_wI,_uK));}),_xe=new T(function(){return B(A1(_wI,_uE));}),_xf=new T(function(){return B(A1(_wI,_uy));}),_xg=new T(function(){return B(A1(_wI,_us));}),_xh=new T(function(){return B(A1(_wI,_um));}),_xi=new T(function(){return B(A1(_wI,_ug));}),_xj=new T(function(){return B(A1(_wI,_sM));}),_xk=new T(function(){return B(A1(_wI,_tu));}),_xl=new T(function(){return B(A1(_wI,_to));}),_xm=new T(function(){return B(A1(_wI,_ti));}),_xn=new T(function(){return B(A1(_wI,_tc));}),_xo=new T(function(){return B(A1(_wI,_t6));}),_xp=new T(function(){return B(A1(_wI,_sS));}),_xq=new T(function(){return B(A1(_wI,_t0));}),_xr=function(_xs){switch(E(_xs)){case 64:return E(_xq);case 65:return E(_xp);case 66:return E(_xo);case 67:return E(_xn);case 68:return E(_xm);case 69:return E(_xl);case 70:return E(_xk);case 71:return E(_wJ);case 72:return E(_wK);case 73:return E(_wL);case 74:return E(_wM);case 75:return E(_wN);case 76:return E(_wO);case 77:return E(_wP);case 78:return E(_xj);case 79:return E(_xi);case 80:return E(_xh);case 81:return E(_xg);case 82:return E(_xf);case 83:return E(_xe);case 84:return E(_xd);case 85:return E(_xc);case 86:return E(_xb);case 87:return E(_xa);case 88:return E(_x9);case 89:return E(_x8);case 90:return E(_x7);case 91:return E(_x6);case 92:return E(_x5);case 93:return E(_x4);case 94:return E(_x3);case 95:return E(_x2);default:return new T0(2);}};return B(_oi(new T1(0,function(_xt){return (E(_xt)==94)?E(new T1(0,_xr)):new T0(2);}),new T(function(){return B(A1(_wC,_wI));})));});return B(_oi(new T1(1,B(_pg(_sj,_sl,_wU))),_x1));});return new F(function(){return _oi(new T1(0,function(_xu){switch(E(_xu)){case 34:return E(_wS);case 39:return E(_wR);case 92:return E(_wQ);case 97:return E(_wJ);case 98:return E(_wK);case 102:return E(_wO);case 110:return E(_wM);case 114:return E(_wP);case 116:return E(_wL);case 118:return E(_wN);default:return new T0(2);}}),_wT);});},_xv=function(_xw){return new F(function(){return A1(_xw,_7f);});},_xx=function(_xy){var _xz=E(_xy);if(!_xz._){return E(_xv);}else{var _xA=E(_xz.a),_xB=_xA>>>0,_xC=new T(function(){return B(_xx(_xz.b));});if(_xB>887){var _xD=u_iswspace(_xA);if(!E(_xD)){return E(_xv);}else{var _xE=function(_xF){var _xG=new T(function(){return B(A1(_xC,_xF));});return new T1(0,function(_xH){return E(_xG);});};return E(_xE);}}else{var _xI=E(_xB);if(_xI==32){var _xJ=function(_xK){var _xL=new T(function(){return B(A1(_xC,_xK));});return new T1(0,function(_xM){return E(_xL);});};return E(_xJ);}else{if(_xI-9>>>0>4){if(E(_xI)==160){var _xN=function(_xO){var _xP=new T(function(){return B(A1(_xC,_xO));});return new T1(0,function(_xQ){return E(_xP);});};return E(_xN);}else{return E(_xv);}}else{var _xR=function(_xS){var _xT=new T(function(){return B(A1(_xC,_xS));});return new T1(0,function(_xU){return E(_xT);});};return E(_xR);}}}}},_xV=function(_xW){var _xX=new T(function(){return B(_xV(_xW));}),_xY=function(_xZ){return (E(_xZ)==92)?E(_xX):new T0(2);},_y0=function(_y1){return E(new T1(0,_xY));},_y2=new T1(1,function(_y3){return new F(function(){return A2(_xx,_y3,_y0);});}),_y4=new T(function(){return B(_wH(function(_y5){return new F(function(){return A1(_xW,new T2(0,_y5,_ls));});}));}),_y6=function(_y7){var _y8=E(_y7);if(_y8==38){return E(_xX);}else{var _y9=_y8>>>0;if(_y9>887){var _ya=u_iswspace(_y8);return (E(_ya)==0)?new T0(2):E(_y2);}else{var _yb=E(_y9);return (_yb==32)?E(_y2):(_yb-9>>>0>4)?(E(_yb)==160)?E(_y2):new T0(2):E(_y2);}}};return new F(function(){return _oi(new T1(0,function(_yc){return (E(_yc)==92)?E(new T1(0,_y6)):new T0(2);}),new T1(0,function(_yd){var _ye=E(_yd);if(E(_ye)==92){return E(_y4);}else{return new F(function(){return A1(_xW,new T2(0,_ye,_sd));});}}));});},_yf=function(_yg,_yh){var _yi=new T(function(){return B(A1(_yh,new T1(1,new T(function(){return B(A1(_yg,_10));}))));}),_yj=function(_yk){var _yl=E(_yk),_ym=E(_yl.a);if(E(_ym)==34){if(!E(_yl.b)){return E(_yi);}else{return new F(function(){return _yf(function(_yn){return new F(function(){return A1(_yg,new T2(1,_ym,_yn));});},_yh);});}}else{return new F(function(){return _yf(function(_yo){return new F(function(){return A1(_yg,new T2(1,_ym,_yo));});},_yh);});}};return new F(function(){return _xV(_yj);});},_yp=new T(function(){return B(unCStr("_\'"));}),_yq=function(_yr){var _ys=u_iswalnum(_yr);if(!E(_ys)){return new F(function(){return _4B(_6f,_yr,_yp);});}else{return true;}},_yt=function(_yu){return new F(function(){return _yq(E(_yu));});},_yv=new T(function(){return B(unCStr(",;()[]{}`"));}),_yw=new T(function(){return B(unCStr("=>"));}),_yx=new T2(1,_yw,_10),_yy=new T(function(){return B(unCStr("~"));}),_yz=new T2(1,_yy,_yx),_yA=new T(function(){return B(unCStr("@"));}),_yB=new T2(1,_yA,_yz),_yC=new T(function(){return B(unCStr("->"));}),_yD=new T2(1,_yC,_yB),_yE=new T(function(){return B(unCStr("<-"));}),_yF=new T2(1,_yE,_yD),_yG=new T(function(){return B(unCStr("|"));}),_yH=new T2(1,_yG,_yF),_yI=new T(function(){return B(unCStr("\\"));}),_yJ=new T2(1,_yI,_yH),_yK=new T(function(){return B(unCStr("="));}),_yL=new T2(1,_yK,_yJ),_yM=new T(function(){return B(unCStr("::"));}),_yN=new T2(1,_yM,_yL),_yO=new T(function(){return B(unCStr(".."));}),_yP=new T2(1,_yO,_yN),_yQ=function(_yR){var _yS=new T(function(){return B(A1(_yR,_pU));}),_yT=new T(function(){var _yU=new T(function(){var _yV=function(_yW){var _yX=new T(function(){return B(A1(_yR,new T1(0,_yW)));});return new T1(0,function(_yY){return (E(_yY)==39)?E(_yX):new T0(2);});};return B(_wH(_yV));}),_yZ=function(_z0){var _z1=E(_z0);switch(E(_z1)){case 39:return new T0(2);case 92:return E(_yU);default:var _z2=new T(function(){return B(A1(_yR,new T1(0,_z1)));});return new T1(0,function(_z3){return (E(_z3)==39)?E(_z2):new T0(2);});}},_z4=new T(function(){var _z5=new T(function(){return B(_yf(_5V,_yR));}),_z6=new T(function(){var _z7=new T(function(){var _z8=new T(function(){var _z9=function(_za){var _zb=E(_za),_zc=u_iswalpha(_zb);return (E(_zc)==0)?(E(_zb)==95)?new T1(1,B(_pG(_yt,function(_zd){return new F(function(){return A1(_yR,new T1(3,new T2(1,_zb,_zd)));});}))):new T0(2):new T1(1,B(_pG(_yt,function(_ze){return new F(function(){return A1(_yR,new T1(3,new T2(1,_zb,_ze)));});})));};return B(_oi(new T1(0,_z9),new T(function(){return new T1(1,B(_pg(_qS,_s8,_yR)));})));}),_zf=function(_zg){return (!B(_4B(_6f,_zg,_sa)))?new T0(2):new T1(1,B(_pG(_sb,function(_zh){var _zi=new T2(1,_zg,_zh);if(!B(_4B(_fp,_zi,_yP))){return new F(function(){return A1(_yR,new T1(4,_zi));});}else{return new F(function(){return A1(_yR,new T1(2,_zi));});}})));};return B(_oi(new T1(0,_zf),_z8));});return B(_oi(new T1(0,function(_zj){if(!B(_4B(_6f,_zj,_yv))){return new T0(2);}else{return new F(function(){return A1(_yR,new T1(2,new T2(1,_zj,_10)));});}}),_z7));});return B(_oi(new T1(0,function(_zk){return (E(_zk)==34)?E(_z5):new T0(2);}),_z6));});return B(_oi(new T1(0,function(_zl){return (E(_zl)==39)?E(new T1(0,_yZ)):new T0(2);}),_z4));});return new F(function(){return _oi(new T1(1,function(_zm){return (E(_zm)._==0)?E(_yS):new T0(2);}),_yT);});},_zn=0,_zo=function(_zp,_zq){var _zr=new T(function(){var _zs=new T(function(){var _zt=function(_zu){var _zv=new T(function(){var _zw=new T(function(){return B(A1(_zq,_zu));});return B(_yQ(function(_zx){var _zy=E(_zx);return (_zy._==2)?(!B(_hq(_zy.a,_oV)))?new T0(2):E(_zw):new T0(2);}));}),_zz=function(_zA){return E(_zv);};return new T1(1,function(_zB){return new F(function(){return A2(_xx,_zB,_zz);});});};return B(A2(_zp,_zn,_zt));});return B(_yQ(function(_zC){var _zD=E(_zC);return (_zD._==2)?(!B(_hq(_zD.a,_oU)))?new T0(2):E(_zs):new T0(2);}));}),_zE=function(_zF){return E(_zr);};return function(_zG){return new F(function(){return A2(_xx,_zG,_zE);});};},_zH=function(_zI,_zJ){var _zK=function(_zL){var _zM=new T(function(){return B(A1(_zI,_zL));}),_zN=function(_zO){return new F(function(){return _oi(B(A1(_zM,_zO)),new T(function(){return new T1(1,B(_zo(_zK,_zO)));}));});};return E(_zN);},_zP=new T(function(){return B(A1(_zI,_zJ));}),_zQ=function(_zR){return new F(function(){return _oi(B(A1(_zP,_zR)),new T(function(){return new T1(1,B(_zo(_zK,_zR)));}));});};return E(_zQ);},_zS=function(_zT,_zU){var _zV=function(_zW,_zX){var _zY=function(_zZ){return new F(function(){return A1(_zX,new T(function(){return  -E(_zZ);}));});},_A0=new T(function(){return B(_yQ(function(_A1){return new F(function(){return A3(_zT,_A1,_zW,_zY);});}));}),_A2=function(_A3){return E(_A0);},_A4=function(_A5){return new F(function(){return A2(_xx,_A5,_A2);});},_A6=new T(function(){return B(_yQ(function(_A7){var _A8=E(_A7);if(_A8._==4){var _A9=E(_A8.a);if(!_A9._){return new F(function(){return A3(_zT,_A8,_zW,_zX);});}else{if(E(_A9.a)==45){if(!E(_A9.b)._){return E(new T1(1,_A4));}else{return new F(function(){return A3(_zT,_A8,_zW,_zX);});}}else{return new F(function(){return A3(_zT,_A8,_zW,_zX);});}}}else{return new F(function(){return A3(_zT,_A8,_zW,_zX);});}}));}),_Aa=function(_Ab){return E(_A6);};return new T1(1,function(_Ac){return new F(function(){return A2(_xx,_Ac,_Aa);});});};return new F(function(){return _zH(_zV,_zU);});},_Ad=function(_Ae){var _Af=E(_Ae);if(!_Af._){var _Ag=_Af.b,_Ah=new T(function(){return B(_rk(new T(function(){return B(_r0(E(_Af.a)));}),new T(function(){return B(_7a(_Ag,0));},1),B(_jH(_r2,_Ag))));});return new T1(1,_Ah);}else{return (E(_Af.b)._==0)?(E(_Af.c)._==0)?new T1(1,new T(function(){return B(_rB(_qZ,_Af.a));})):__Z:__Z;}},_Ai=function(_Aj,_Ak){return new T0(2);},_Al=function(_Am){var _An=E(_Am);if(_An._==5){var _Ao=B(_Ad(_An.a));if(!_Ao._){return E(_Ai);}else{var _Ap=new T(function(){return B(_8n(_Ao.a));});return function(_Aq,_Ar){return new F(function(){return A1(_Ar,_Ap);});};}}else{return E(_Ai);}},_As=function(_At){var _Au=function(_Av){return E(new T2(3,_At,_p7));};return new T1(1,function(_Aw){return new F(function(){return A2(_xx,_Aw,_Au);});});},_Ax=new T(function(){return B(A3(_zS,_Al,_zn,_As));}),_Ay=new T(function(){return B(_a2("Event.hs:(26,1)-(31,74)|function putCell"));}),_Az=function(_AA){while(1){var _AB=B((function(_AC){var _AD=E(_AC);if(!_AD._){return __Z;}else{var _AE=_AD.b,_AF=E(_AD.a);if(!E(_AF.b)._){return new T2(1,_AF.a,new T(function(){return B(_Az(_AE));}));}else{_AA=_AE;return __continue;}}})(_AA));if(_AB!=__continue){return _AB;}}},_AG=function(_AH,_AI,_AJ,_AK,_AL,_AM,_AN,_AO,_AP,_AQ,_AR,_AS,_AT,_AU,_AV,_AW,_AX,_AY,_AZ,_B0,_B1,_B2,_B3,_B4,_B5,_B6,_B7,_B8,_B9,_Ba,_Bb){while(1){var _Bc=B((function(_Bd,_Be,_Bf,_Bg,_Bh,_Bi,_Bj,_Bk,_Bl,_Bm,_Bn,_Bo,_Bp,_Bq,_Br,_Bs,_Bt,_Bu,_Bv,_Bw,_Bx,_By,_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG,_BH){var _BI=E(_Bd);if(!_BI._){return {_:0,a:_Be,b:_Bf,c:_Bg,d:_Bh,e:_Bi,f:_Bj,g:_Bk,h:_Bl,i:_Bm,j:_Bn,k:_Bo,l:_Bp,m:_Bq,n:_Br,o:_Bs,p:_Bt,q:_Bu,r:_Bv,s:_Bw,t:_Bx,u:_By,v:_Bz,w:_BA,x:_BB,y:_BC,z:_BD,A:_BE,B:_BF,C:_BG,D:_BH};}else{var _BJ=E(_BI.b);if(!_BJ._){return E(_Ay);}else{var _BK=new T(function(){var _BL=E(_BI.a);if(!_BL._){return E(_o3);}else{var _BM=E(_BL.b);if(!_BM._){return E(_o3);}else{var _BN=_BM.a,_BO=_BM.b,_BP=E(_BL.a);if(E(_BP)==44){return new T2(0,_10,new T(function(){return E(B(_lz(44,_BN,_BO)).a);}));}else{var _BQ=B(_lz(44,_BN,_BO)),_BR=E(_BQ.b);if(!_BR._){return E(_o3);}else{return new T2(0,new T2(1,_BP,_BQ.a),_BR.a);}}}}}),_BS=B(_Az(B(_o8(_Ax,new T(function(){return E(E(_BK).b);})))));if(!_BS._){return E(_nY);}else{if(!E(_BS.b)._){var _BT=new T(function(){var _BU=E(_BJ.a);if(!_BU._){return E(_o6);}else{var _BV=E(_BU.b);if(!_BV._){return E(_o6);}else{var _BW=_BV.a,_BX=_BV.b,_BY=E(_BU.a);if(E(_BY)==44){return new T2(0,_10,new T(function(){return E(B(_lz(44,_BW,_BX)).a);}));}else{var _BZ=B(_lz(44,_BW,_BX)),_C0=E(_BZ.b);if(!_C0._){return E(_o6);}else{return new T2(0,new T2(1,_BY,_BZ.a),_C0.a);}}}}}),_C1=new T(function(){var _C2=B(_Az(B(_o8(_Ax,new T(function(){return E(E(_BK).a);})))));if(!_C2._){return E(_nY);}else{if(!E(_C2.b)._){return E(_C2.a);}else{return E(_o0);}}},1),_C3=_Be,_C4=_Bf,_C5=B(_ny(_C1,E(_BS.a),new T(function(){return B(_hm(E(_BT).a));}),new T(function(){return B(_hF(E(_BT).b));}),_Bg)),_C6=_Bh,_C7=_Bi,_C8=_Bj,_C9=_Bk,_Ca=_Bl,_Cb=_Bm,_Cc=_Bn,_Cd=_Bo,_Ce=_Bp,_Cf=_Bq,_Cg=_Br,_Ch=_Bs,_Ci=_Bt,_Cj=_Bu,_Ck=_Bv,_Cl=_Bw,_Cm=_Bx,_Cn=_By,_Co=_Bz,_Cp=_BA,_Cq=_BB,_Cr=_BC,_Cs=_BD,_Ct=_BE,_Cu=_BF,_Cv=_BG,_Cw=_BH;_AH=_BJ.b;_AI=_C3;_AJ=_C4;_AK=_C5;_AL=_C6;_AM=_C7;_AN=_C8;_AO=_C9;_AP=_Ca;_AQ=_Cb;_AR=_Cc;_AS=_Cd;_AT=_Ce;_AU=_Cf;_AV=_Cg;_AW=_Ch;_AX=_Ci;_AY=_Cj;_AZ=_Ck;_B0=_Cl;_B1=_Cm;_B2=_Cn;_B3=_Co;_B4=_Cp;_B5=_Cq;_B6=_Cr;_B7=_Cs;_B8=_Ct;_B9=_Cu;_Ba=_Cv;_Bb=_Cw;return __continue;}else{return E(_o0);}}}}})(_AH,_AI,_AJ,_AK,_AL,_AM,_AN,_AO,_AP,_AQ,_AR,_AS,_AT,_AU,_AV,_AW,_AX,_AY,_AZ,_B0,_B1,_B2,_B3,_B4,_B5,_B6,_B7,_B8,_B9,_Ba,_Bb));if(_Bc!=__continue){return _Bc;}}},_Cx=function(_Cy){var _Cz=E(_Cy);if(!_Cz._){return new T2(0,_10,_10);}else{var _CA=E(_Cz.a),_CB=new T(function(){var _CC=B(_Cx(_Cz.b));return new T2(0,_CC.a,_CC.b);});return new T2(0,new T2(1,_CA.a,new T(function(){return E(E(_CB).a);})),new T2(1,_CA.b,new T(function(){return E(E(_CB).b);})));}},_CD=0,_CE=0,_CF=32,_CG=function(_CH,_CI,_CJ,_CK){var _CL=E(_CK);if(!_CL._){return __Z;}else{var _CM=_CL.b;if(!B(_4B(_3M,_CH,_CJ))){var _CN=new T(function(){return B(_CG(new T(function(){return E(_CH)+1|0;}),_CI,_CJ,_CM));});return new T2(1,_CL.a,_CN);}else{var _CO=new T(function(){return B(_CG(new T(function(){return E(_CH)+1|0;}),_CI,_CJ,_CM));});return new T2(1,_CI,_CO);}}},_CP=function(_CQ,_CR){var _CS=E(_CR);if(!_CS._){return __Z;}else{var _CT=new T(function(){var _CU=B(_Cx(_CS.a)),_CV=_CU.a,_CW=new T(function(){return B(_gU(0,_CQ,_CV));});return B(_h8(B(_CG(_CE,_CF,_CW,_CV)),new T(function(){return B(_h1(0,_CD,_CW,_CU.b));},1)));});return new T2(1,_CT,new T(function(){return B(_CP(_CQ,_CS.b));}));}},_CX=function(_CY,_CZ){var _D0=E(_CZ);return (_D0._==0)?__Z:new T2(1,_CY,new T(function(){return B(_CX(_D0.a,_D0.b));}));},_D1=new T(function(){return B(unCStr("init"));}),_D2=new T(function(){return B(_dG(_D1));}),_D3=function(_D4,_D5){var _D6=function(_D7){var _D8=E(_D7);if(!_D8._){return __Z;}else{var _D9=new T(function(){return B(_y(new T2(1,_D4,_10),new T(function(){return B(_D6(_D8.b));},1)));},1);return new F(function(){return _y(_D8.a,_D9);});}},_Da=B(_D6(_D5));if(!_Da._){return E(_D2);}else{return new F(function(){return _CX(_Da.a,_Da.b);});}},_Db=61,_Dc=46,_Dd=new T(function(){return B(_a2("Event.hs:(67,1)-(73,61)|function makeDecision"));}),_De=new T(function(){return B(unCStr("if"));}),_Df=new T(function(){return B(unCStr("ch"));}),_Dg=new T(function(){return B(unCStr("cleq"));}),_Dh=new T(function(){return B(unCStr("da"));}),_Di=new T(function(){return B(unCStr("ct"));}),_Dj=function(_Dk,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO){var _DP=function(_DQ,_DR){var _DS=function(_DT){if(!B(_hq(_DQ,_Di))){if(!B(_hq(_DQ,_Dh))){var _DU=function(_DV){if(!B(_hq(_DQ,_Dg))){var _DW=function(_DX){if(!B(_hq(_DQ,_Df))){if(!B(_hq(_DQ,_De))){return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}else{var _DY=E(_DR);if(!_DY._){return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}else{var _DZ=_DY.a,_E0=E(_DY.b);if(!_E0._){return E(_Dd);}else{var _E1=_E0.a,_E2=B(_lm(_Dv)),_E3=_E2.a,_E4=_E2.b,_E5=function(_E6){if(!B(_4B(_fp,_DZ,_E3))){return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}else{if(!B(_hq(_E1,B(_77(_E4,B(_jf(_fp,_DZ,_E3))))))){return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}else{return new F(function(){return _Dj(_E6,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}}},_E7=B(_D3(_Dc,_E0.b));if(!_E7._){return new F(function(){return _E5(_10);});}else{var _E8=_E7.a,_E9=E(_E7.b);if(!_E9._){return new F(function(){return _E5(new T2(1,_E8,_10));});}else{var _Ea=_E9.a,_Eb=_E9.b,_Ec=E(_E8);if(E(_Ec)==47){if(!B(_4B(_fp,_DZ,_E3))){return new F(function(){return _Dj(B(_lz(47,_Ea,_Eb)).a,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}else{if(!B(_hq(_E1,B(_77(_E4,B(_jf(_fp,_DZ,_E3))))))){return new F(function(){return _Dj(B(_lz(47,_Ea,_Eb)).a,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}else{return new F(function(){return _Dj(_10,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}}}else{if(!B(_4B(_fp,_DZ,_E3))){var _Ed=E(B(_lz(47,_Ea,_Eb)).b);if(!_Ed._){return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}else{return new F(function(){return _Dj(_Ed.a,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}}else{if(!B(_hq(_E1,B(_77(_E4,B(_jf(_fp,_DZ,_E3))))))){var _Ee=E(B(_lz(47,_Ea,_Eb)).b);if(!_Ee._){return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}else{return new F(function(){return _Dj(_Ee.a,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}}else{return new F(function(){return _Dj(new T2(1,_Ec,new T(function(){return E(B(_lz(47,_Ea,_Eb)).a);})),_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}}}}}}}}}else{return new F(function(){return _lH(_DR,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO);});}},_Ef=E(_DQ);if(!_Ef._){return new F(function(){return _DW(_);});}else{if(E(_Ef.a)==109){if(!E(_Ef.b)._){var _Eg=B(_g3(_DR,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO));return {_:0,a:E(_Eg.a),b:E(_Eg.b),c:E(_Eg.c),d:_Eg.d,e:_Eg.e,f:_Eg.f,g:E(_Eg.g),h:E(_Eg.h),i:E(_Eg.i),j:E(_Eg.j),k:E(_Eg.k),l:E(_Eg.l),m:_Eg.m,n:_Eg.n,o:_Eg.o,p:_Eg.p,q:_Eg.q,r:E(_Eg.r),s:_Eg.s,t:E(_Eg.t),u:E(_Eg.u),v:E(_Eg.v),w:E(_Eg.w),x:E(_Eg.x),y:E(_Eg.y),z:E(_Eg.z),A:E(_Eg.A),B:E(_Eg.B),C:E(_Eg.C),D:_Eg.D};}else{return new F(function(){return _DW(_);});}}else{return new F(function(){return _DW(_);});}}}else{return {_:0,a:E(_Dl),b:E(_Dm),c:E(B(_CP(_Db,_Dn))),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_Ds),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}},_Eh=E(_DQ);if(!_Eh._){return new F(function(){return _DU(_);});}else{if(E(_Eh.a)==112){if(!E(_Eh.b)._){var _Ei=B(_AG(_DR,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO));return {_:0,a:E(_Ei.a),b:E(_Ei.b),c:E(_Ei.c),d:_Ei.d,e:_Ei.e,f:_Ei.f,g:E(_Ei.g),h:E(_Ei.h),i:E(_Ei.i),j:E(_Ei.j),k:E(_Ei.k),l:E(_Ei.l),m:_Ei.m,n:_Ei.n,o:_Ei.o,p:_Ei.p,q:_Ei.q,r:E(_Ei.r),s:_Ei.s,t:E(_Ei.t),u:E(_Ei.u),v:E(_Ei.v),w:E(_Ei.w),x:E(_Ei.x),y:E(_Ei.y),z:E(_Ei.z),A:E(_Ei.A),B:E(_Ei.B),C:E(_Ei.C),D:_Ei.D};}else{return new F(function(){return _DU(_);});}}else{return new F(function(){return _DU(_);});}}}else{return {_:0,a:E(_Dl),b:E(_Dm),c:E(_Dn),d:_Do,e:_Dp,f:_Dq,g:E(_Dr),h:E(_10),i:E(_Dt),j:E(_Du),k:E(_Dv),l:E(_Dw),m:_Dx,n:_Dy,o:_Dz,p:_DA,q:_DB,r:E(_DC),s:_DD,t:E(_DE),u:E(_DF),v:E(_DG),w:E(_DH),x:E(_DI),y:E(_DJ),z:E(_DK),A:E(_DL),B:E(_DM),C:E(_DN),D:_DO};}}else{var _Ej=B(_hH(_DR,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO));return {_:0,a:E(_Ej.a),b:E(_Ej.b),c:E(_Ej.c),d:_Ej.d,e:_Ej.e,f:_Ej.f,g:E(_Ej.g),h:E(_Ej.h),i:E(_Ej.i),j:E(_Ej.j),k:E(_Ej.k),l:E(_Ej.l),m:_Ej.m,n:_Ej.n,o:_Ej.o,p:_Ej.p,q:_Ej.q,r:E(_Ej.r),s:_Ej.s,t:E(_Ej.t),u:E(_Ej.u),v:E(_Ej.v),w:E(_Ej.w),x:E(_Ej.x),y:E(_Ej.y),z:E(_Ej.z),A:E(_Ej.A),B:E(_Ej.B),C:E(_Ej.C),D:_Ej.D};}},_Ek=E(_DQ);if(!_Ek._){return new F(function(){return _DS(_);});}else{var _El=_Ek.b;switch(E(_Ek.a)){case 100:if(!E(_El)._){var _Em=B(_jL(_DR,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO));return {_:0,a:E(_Em.a),b:E(_Em.b),c:E(_Em.c),d:_Em.d,e:_Em.e,f:_Em.f,g:E(_Em.g),h:E(_Em.h),i:E(_Em.i),j:E(_Em.j),k:E(_Em.k),l:E(_Em.l),m:_Em.m,n:_Em.n,o:_Em.o,p:_Em.p,q:_Em.q,r:E(_Em.r),s:_Em.s,t:E(_Em.t),u:E(_Em.u),v:E(_Em.v),w:E(_Em.w),x:E(_Em.x),y:E(_Em.y),z:E(_Em.z),A:E(_Em.A),B:E(_Em.B),C:E(_Em.C),D:_Em.D};}else{return new F(function(){return _DS(_);});}break;case 101:if(!E(_El)._){var _En=B(_fs(_DR,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD,_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO));return {_:0,a:E(_En.a),b:E(_En.b),c:E(_En.c),d:_En.d,e:_En.e,f:_En.f,g:E(_En.g),h:E(_En.h),i:E(_En.i),j:E(_En.j),k:E(_En.k),l:E(_En.l),m:_En.m,n:_En.n,o:_En.o,p:_En.p,q:_En.q,r:E(_En.r),s:_En.s,t:E(_En.t),u:E(_En.u),v:E(_En.v),w:E(_En.w),x:E(_En.x),y:E(_En.y),z:E(_En.z),A:E(_En.A),B:E(_En.B),C:E(_En.C),D:_En.D};}else{return new F(function(){return _DS(_);});}break;default:return new F(function(){return _DS(_);});}}},_Eo=E(_Dk);if(!_Eo._){return new F(function(){return _DP(_10,_10);});}else{var _Ep=_Eo.a,_Eq=E(_Eo.b);if(!_Eq._){return new F(function(){return _DP(new T2(1,_Ep,_10),_10);});}else{var _Er=E(_Ep),_Es=new T(function(){var _Et=B(_lz(46,_Eq.a,_Eq.b));return new T2(0,_Et.a,_Et.b);});if(E(_Er)==46){return new F(function(){return _DP(_10,new T2(1,new T(function(){return E(E(_Es).a);}),new T(function(){return E(E(_Es).b);})));});}else{return new F(function(){return _DP(new T2(1,_Er,new T(function(){return E(E(_Es).a);})),new T(function(){return E(E(_Es).b);}));});}}}},_Eu=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_Ev=new T(function(){return eval("(function(ctx){ctx.save();})");}),_Ew=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_Ex=function(_Ey,_Ez,_EA,_){var _EB=__app1(E(_Ev),_EA),_EC=__app2(E(_Ew),_EA,E(_Ey)),_ED=B(A2(_Ez,_EA,_)),_EE=__app1(E(_Eu),_EA);return new F(function(){return _7g(_);});},_EF=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_EG=function(_EH,_EI,_EJ,_EK,_){var _EL=__app1(E(_Ev),_EK),_EM=__app3(E(_EF),_EK,E(_EH),E(_EI)),_EN=B(A2(_EJ,_EK,_)),_EO=__app1(E(_Eu),_EK);return new F(function(){return _7g(_);});},_EP=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e"));}),_EQ=function(_ER){if(_ER<=31){return new F(function(){return _4B(_6f,_ER,_EP);});}else{if(_ER>=128){return new F(function(){return _4B(_6f,_ER,_EP);});}else{return true;}}},_ES=1.5707963267948966,_ET=new T(function(){return B(unCStr("px VL Gothic"));}),_EU=function(_EV,_EW,_EX,_EY,_EZ,_F0,_F1){var _F2=new T(function(){var _F3=new T(function(){if(E(_EX)==8){return new T2(0,new T(function(){return E(_EZ)*28+20;}),new T(function(){return E(_F0)*20+8*(E(_EY)-1);}));}else{return new T2(0,new T(function(){return E(_EZ)*28;}),new T(function(){return E(_F0)*20;}));}}),_F4=new T(function(){return B(_EQ(E(_F1)));}),_F5=new T(function(){var _F6=E(E(_F3).a);if(!E(_F4)){return E(_F6);}else{return _F6+3.3333333333333335;}}),_F7=new T(function(){var _F8=E(E(_F3).b);if(!E(_F4)){return E(_F8);}else{return _F8-16.666666666666668;}}),_F9=new T(function(){if(!E(_F4)){return E(_cl);}else{return E(_ES);}}),_Fa=new T(function(){return B(_7i(_cl,_cl,new T2(1,_F1,_10)));}),_Fb=function(_Fc,_){return new F(function(){return _Ex(_F9,_Fa,E(_Fc),_);});};return B(_d3(new T(function(){return B(_y(B(_I(0,E(_EX),_10)),_ET));},1),function(_Fd,_){return new F(function(){return _EG(_F5,_F7,_Fb,E(_Fd),_);});}));});return new F(function(){return A3(_cI,_EW,_F2,_EV);});},_Fe=15,_Ff=new T(function(){return B(unCStr("last"));}),_Fg=new T(function(){return B(_dG(_Ff));}),_Fh=27,_Fi=1,_Fj=65306,_Fk=125,_Fl=function(_Fm){return E(E(_Fm).b);},_Fn=function(_Fo,_Fp,_Fq){var _Fr=E(_Fp),_Fs=E(_Fq),_Ft=new T(function(){var _Fu=B(_c8(_Fo)),_Fv=B(_Fn(_Fo,_Fs,B(A3(_Fl,_Fu,new T(function(){return B(A3(_ca,_Fu,_Fs,_Fs));}),_Fr))));return new T2(1,_Fv.a,_Fv.b);});return new T2(0,_Fr,_Ft);},_Fw=1,_Fx=new T(function(){var _Fy=B(_Fn(_c6,_cl,_Fw));return new T2(1,_Fy.a,_Fy.b);}),_Fz=42,_FA=function(_FB,_FC,_FD){var _FE=E(_FB);if(!_FE._){return __Z;}else{var _FF=_FE.a,_FG=_FE.b;if(_FC!=_FD){var _FH=E(_FF);return (_FH._==0)?E(_dJ):(E(_FH.a)==42)?new T2(1,new T2(1,_dN,_FH.b),new T(function(){return B(_FA(_FG,_FC,_FD+1|0));})):new T2(1,new T2(1,_dN,_FH),new T(function(){return B(_FA(_FG,_FC,_FD+1|0));}));}else{var _FI=E(_FF);return (_FI._==0)?E(_dJ):(E(_FI.a)==42)?new T2(1,new T2(1,_dN,_FI),new T(function(){return B(_FA(_FG,_FC,_FD+1|0));})):new T2(1,new T2(1,_Fz,_FI),new T(function(){return B(_FA(_FG,_FC,_FD+1|0));}));}}},_FJ=function(_FK,_FL,_FM){var _FN=E(_FK);if(!_FN._){return __Z;}else{var _FO=_FN.a,_FP=_FN.b,_FQ=E(_FL);if(_FQ!=_FM){var _FR=E(_FO);return (_FR._==0)?E(_dJ):(E(_FR.a)==42)?new T2(1,new T2(1,_dN,_FR.b),new T(function(){return B(_FA(_FP,_FQ,_FM+1|0));})):new T2(1,new T2(1,_dN,_FR),new T(function(){return B(_FA(_FP,_FQ,_FM+1|0));}));}else{var _FS=E(_FO);return (_FS._==0)?E(_dJ):(E(_FS.a)==42)?new T2(1,new T2(1,_dN,_FS),new T(function(){return B(_FA(_FP,_FQ,_FM+1|0));})):new T2(1,new T2(1,_Fz,_FS),new T(function(){return B(_FA(_FP,_FQ,_FM+1|0));}));}}},_FT=new T(function(){return B(unCStr("\n\n"));}),_FU=function(_FV){var _FW=E(_FV);if(!_FW._){return __Z;}else{var _FX=new T(function(){return B(_y(_FT,new T(function(){return B(_FU(_FW.b));},1)));},1);return new F(function(){return _y(_FW.a,_FX);});}},_FY=function(_FZ,_G0,_G1){var _G2=new T(function(){return B(unAppCStr("\n\n",new T(function(){return B(_FU(B(_FJ(_G0,_G1,0))));})));},1);return new F(function(){return _y(_FZ,_G2);});},_G3=20,_G4=64,_G5=3,_G6=0,_G7=function(_G8,_G9,_Ga,_Gb,_Gc,_Gd,_){while(1){var _Ge=B((function(_Gf,_Gg,_Gh,_Gi,_Gj,_Gk,_){var _Gl=E(_Gk);if(!_Gl._){return _7f;}else{var _Gm=_Gl.b;if(E(_Gl.a)==125){var _Gn=new T(function(){var _Go=E(_Gj);if((_Go+1)*20<=557){return new T2(0,_Gi,_Go+1|0);}else{return new T2(0,new T(function(){return E(_Gi)-1|0;}),_Gh);}});return new F(function(){return _Gp(_Gf,_Gg,_Gh,new T(function(){return E(E(_Gn).a);}),new T(function(){return E(E(_Gn).b);}),_Gm,_);});}else{var _Gq=_Gf,_Gr=_Gg,_Gs=_Gh,_Gt=_Gi,_Gu=_Gj;_G8=_Gq;_G9=_Gr;_Ga=_Gs;_Gb=_Gt;_Gc=_Gu;_Gd=_Gm;return __continue;}}})(_G8,_G9,_Ga,_Gb,_Gc,_Gd,_));if(_Ge!=__continue){return _Ge;}}},_Gp=function(_Gv,_Gw,_Gx,_Gy,_Gz,_GA,_){while(1){var _GB=B((function(_GC,_GD,_GE,_GF,_GG,_GH,_){var _GI=E(_GH);if(!_GI._){return _7f;}else{var _GJ=_GI.b,_GK=E(_GI.a),_GL=E(_GK);switch(_GL){case 10:var _GM=_GC,_GN=_GE,_GO=_GE;_Gv=_GM;_Gw=_G6;_Gx=_GN;_Gy=new T(function(){return E(_GF)-1|0;});_Gz=_GO;_GA=_GJ;return __continue;case 123:return new F(function(){return _G7(_GC,_GD,_GE,_GF,_GG,_GJ,_);});break;case 65306:return new F(function(){return A(_GP,[_GC,_GD,_GE,new T(function(){if(E(_GE)!=E(_GG)){return E(_GF);}else{return E(_GF)+1|0;}}),new T(function(){var _GQ=E(_GG);if(E(_GE)!=_GQ){return _GQ-1|0;}else{return E(_Fh);}}),_GJ,_]);});break;default:var _GR=function(_GS,_GT){var _GU=new T(function(){switch(E(_GL)){case 42:return E(_G5);break;case 12300:return E(_Fi);break;default:return E(_GD);}}),_GV=function(_){var _GW=new T(function(){var _GX=E(_GG);if((_GX+1)*20<=557){return new T2(0,_GF,_GX+1|0);}else{return new T2(0,new T(function(){return E(_GF)-1|0;}),_GE);}});return new F(function(){return _Gp(_GC,_GU,_GE,new T(function(){return E(E(_GW).a);}),new T(function(){return E(E(_GW).b);}),_GJ,_);});};if(E(_GS)==64){return new F(function(){return _GV(_);});}else{var _GY=B(A(_EU,[E(_GC).a,new T(function(){return B(_77(_em,E(_GU)));},1),_G3,_cl,_GF,_GG,_GT,_]));return new F(function(){return _GV(_);});}},_GZ=E(_GL);switch(_GZ){case 42:return new F(function(){return _GR(64,_G4);});break;case 12289:return new F(function(){return _GR(64,_G4);});break;case 12290:return new F(function(){return _GR(64,_G4);});break;default:return new F(function(){return _GR(_GZ,_GK);});}}}})(_Gv,_Gw,_Gx,_Gy,_Gz,_GA,_));if(_GB!=__continue){return _GB;}}},_H0=8,_GP=function(_H1,_H2,_H3,_H4,_H5){var _H6=new T(function(){return B(_77(_em,E(_H2)));}),_H7=function(_H8,_H9,_Ha,_Hb,_Hc,_Hd,_He,_){while(1){var _Hf=B((function(_Hg,_Hh,_Hi,_Hj,_Hk,_Hl,_Hm,_){var _Hn=E(_Hm);if(!_Hn._){return _7f;}else{var _Ho=_Hn.b,_Hp=E(_Hn.a);if(E(_Hp)==65306){var _Hq=new T(function(){var _Hr=E(_Hl);if((_Hr+1)*20<=557){return new T2(0,_Hk,_Hr+1|0);}else{return new T2(0,new T(function(){return E(_Hk)-1|0;}),_Hi);}});return new F(function(){return _Hs(_Hg,_Hh,_H2,_Hi,new T(function(){return E(E(_Hq).a);}),new T(function(){return E(E(_Hq).b);}),_Ho,_);});}else{var _Ht=B(A(_EU,[_Hg,_H6,_H0,_Hj,_Hk,_Hl,_Hp,_])),_Hu=_Hg,_Hv=_Hh,_Hw=_Hi,_Hx=_Hk,_Hy=_Hl;_H8=_Hu;_H9=_Hv;_Ha=_Hw;_Hb=new T(function(){return E(_Hj)+1;});_Hc=_Hx;_Hd=_Hy;_He=_Ho;return __continue;}}})(_H8,_H9,_Ha,_Hb,_Hc,_Hd,_He,_));if(_Hf!=__continue){return _Hf;}}},_Hz=function(_HA,_){var _HB=E(_HA);if(!_HB._){return _7f;}else{var _HC=_HB.b,_HD=E(_HB.a);if(E(_HD)==65306){var _HE=new T(function(){var _HF=E(_H5);if((_HF+1)*20<=557){return new T2(0,_H4,_HF+1|0);}else{return new T2(0,new T(function(){return E(_H4)-1|0;}),_H3);}});return new F(function(){return _Gp(_H1,_H2,_H3,new T(function(){return E(E(_HE).a);}),new T(function(){return E(E(_HE).b);}),_HC,_);});}else{var _HG=E(_H1),_HH=_HG.a,_HI=B(A(_EU,[_HH,_H6,_H0,_cl,_H4,_H5,_HD,_]));return new F(function(){return _H7(_HH,_HG.b,_H3,1,_H4,_H5,_HC,_);});}}};return E(_Hz);},_Hs=function(_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_){while(1){var _HQ=B((function(_HR,_HS,_HT,_HU,_HV,_HW,_HX,_){var _HY=E(_HX);if(!_HY._){return _7f;}else{var _HZ=_HY.b,_I0=E(_HY.a),_I1=E(_I0);switch(_I1){case 10:var _I2=_HR,_I3=_HS,_I4=_HU,_I5=_HU;_HJ=_I2;_HK=_I3;_HL=_G6;_HM=_I4;_HN=new T(function(){return E(_HV)-1|0;});_HO=_I5;_HP=_HZ;return __continue;case 123:return new F(function(){return _G7(new T2(0,_HR,_HS),_HT,_HU,_HV,_HW,_HZ,_);});break;case 65306:return new F(function(){return A(_GP,[new T2(0,_HR,_HS),_HT,_HU,new T(function(){if(E(_HU)!=E(_HW)){return E(_HV);}else{return E(_HV)+1|0;}}),new T(function(){var _I6=E(_HW);if(E(_HU)!=_I6){return _I6-1|0;}else{return E(_Fh);}}),_HZ,_]);});break;default:var _I7=function(_I8,_I9){var _Ia=new T(function(){switch(E(_I1)){case 42:return E(_G5);break;case 12300:return E(_Fi);break;default:return E(_HT);}}),_Ib=function(_){var _Ic=new T(function(){var _Id=E(_HW);if((_Id+1)*20<=557){return new T2(0,_HV,_Id+1|0);}else{return new T2(0,new T(function(){return E(_HV)-1|0;}),_HU);}});return new F(function(){return _Hs(_HR,_HS,_Ia,_HU,new T(function(){return E(E(_Ic).a);}),new T(function(){return E(E(_Ic).b);}),_HZ,_);});};if(E(_I8)==64){return new F(function(){return _Ib(_);});}else{var _Ie=B(A(_EU,[_HR,new T(function(){return B(_77(_em,E(_Ia)));},1),_G3,_cl,_HV,_HW,_I9,_]));return new F(function(){return _Ib(_);});}},_If=E(_I1);switch(_If){case 42:return new F(function(){return _I7(64,_G4);});break;case 12289:return new F(function(){return _I7(64,_G4);});break;case 12290:return new F(function(){return _I7(64,_G4);});break;default:return new F(function(){return _I7(_If,_I0);});}}}})(_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_));if(_HQ!=__continue){return _HQ;}}},_Ig=function(_Ih,_Ii,_Ij,_Ik,_Il,_Im,_In,_Io,_Ip,_Iq,_Ir,_Is,_It,_Iu,_Iv,_Iw,_Ix,_Iy,_Iz,_IA,_IB,_IC,_ID,_IE,_IF,_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN,_){var _IO=new T2(0,_Iu,_Iv);if(!E(_IG)){return {_:0,a:E(_Ii),b:E(new T2(0,_Ij,_Ik)),c:E(_Il),d:_Im,e:_In,f:_Io,g:E(_Ip),h:E(_Iq),i:E(_Ir),j:E(_Is),k:E(_It),l:E(_IO),m:_Iw,n:_Ix,o:_Iy,p:_Iz,q:_IA,r:E(_IB),s:_IC,t:E(_ID),u:E(_IE),v:E(_IF),w:E(_sd),x:E(_IH),y:E(_II),z:E(_IJ),A:E(_IK),B:E(_IL),C:E(_IM),D:_IN};}else{if(!E(_IH)){var _IP=_Iw+1|0;if(0>=_IP){return E(_Fg);}else{var _IQ=B(_f4(_Ip,_IP,_Fg)),_IR=function(_IS){if(E(_IS)==65306){var _IT=true;}else{var _IT=false;}var _IU=new T(function(){if(E(_IS)==10){return true;}else{return false;}}),_IV=new T(function(){if(!E(_IU)){if(E(_IS)==12300){return E(_Fi);}else{return _Ix;}}else{return E(_G6);}}),_IW=new T(function(){return B(_77(_em,E(_IV)));}),_IX=new T(function(){return (2+E(_Ik)|0)+3|0;}),_IY=new T(function(){if(!E(_Iw)){return new T2(0,_Fe,_IX);}else{return E(_IO);}}),_IZ=new T(function(){return E(E(_IY).a);}),_J0=new T(function(){return E(E(_IY).b);}),_J1=new T(function(){if(!E(_IT)){if(!E(_IU)){var _J2=E(_J0);if((_J2+1)*20<=557){return new T2(0,_IZ,_J2+1|0);}else{return new T2(0,new T(function(){return E(_IZ)-1|0;}),_IX);}}else{return new T2(0,new T(function(){return E(_IZ)-1|0;}),_IX);}}else{return new T2(0,_IZ,_J0);}}),_J3=new T(function(){if(E(E(_J1).a)==1){if(E(_IZ)==1){return false;}else{return true;}}else{return false;}}),_J4=new T(function(){if(!E(_IT)){return __Z;}else{return B(_eZ(_Fj,_Iw,_Ip));}}),_J5=new T(function(){if(E(_IS)==123){return true;}else{return false;}}),_J6=new T(function(){if(!E(_J5)){return __Z;}else{return B(_eZ(_Fk,_Iw,_Ip));}}),_J7=new T(function(){if(!E(_J5)){if(E(_IQ)==12290){var _J8=true;}else{var _J8=false;}return {_:0,a:E(_Ii),b:E(new T2(0,_Ij,_Ik)),c:E(_Il),d:_Im,e:_In,f:_Io,g:E(_Ip),h:E(_Iq),i:E(_Ir),j:E(_Is),k:E(_It),l:E(_IO),m:_Iw,n:_Ix,o:_Iy,p:_Iz,q:_IA,r:E(_IB),s:_IC,t:E(_ID),u:E(_IE),v:E(_IF),w:E(_ls),x:E(_J8),y:E(_II),z:E(_IJ),A:E(_IK),B:E(_IL),C:E(_IM),D:_IN};}else{if(E(_IQ)==12290){var _J9=true;}else{var _J9=false;}return B(_Dj(_J6,_Ii,new T2(0,_Ij,_Ik),_Il,_Im,_In,_Io,_Ip,_Iq,_Ir,_Is,_It,_IO,_Iw,_Ix,_Iy,_Iz,_IA,_IB,_IC,_ID,_IE,_IF,_ls,_J9,_II,_IJ,_IK,_IL,_IM,_IN));}}),_Ja=new T(function(){if(!E(_Iw)){return E(_G6);}else{return E(_J7).o;}}),_Jb=function(_){return new T(function(){var _Jc=E(_J7),_Jd=_Jc.a,_Je=_Jc.b,_Jf=_Jc.c,_Jg=_Jc.d,_Jh=_Jc.e,_Ji=_Jc.f,_Jj=_Jc.g,_Jk=_Jc.h,_Jl=_Jc.i,_Jm=_Jc.j,_Jn=_Jc.k,_Jo=_Jc.p,_Jp=_Jc.q,_Jq=_Jc.r,_Jr=_Jc.s,_Js=_Jc.t,_Jt=_Jc.u,_Ju=_Jc.v,_Jv=_Jc.x,_Jw=_Jc.y,_Jx=_Jc.z,_Jy=_Jc.A,_Jz=_Jc.B,_JA=_Jc.C,_JB=_Jc.D;if(!E(_J3)){var _JC=E(_J1);}else{var _JC=new T2(0,_IZ,_IX);}var _JD=function(_JE){var _JF=B(_7a(_Ip,0))-1|0;if((_Iw+_JE|0)<=_JF){var _JG=E(_IV);return (!E(_J3))?{_:0,a:E(_Jd),b:E(_Je),c:E(_Jf),d:_Jg,e:_Jh,f:_Ji,g:E(_Jj),h:E(_Jk),i:E(_Jl),j:E(_Jm),k:E(_Jn),l:E(_JC),m:_Iw+_JE|0,n:_JG,o:E(_Ja),p:_Jo,q:_Jp,r:E(_Jq),s:_Jr,t:E(_Js),u:E(_Jt),v:E(_Ju),w:(_Iw+_JE|0)<=_JF,x:E(_Jv),y:E(_Jw),z:E(_Jx),A:E(_Jy),B:E(_Jz),C:E(_JA),D:_JB}:{_:0,a:E(_Jd),b:E(_Je),c:E(_Jf),d:_Jg,e:_Jh,f:_Ji,g:E(_Jj),h:E(_Jk),i:E(_Jl),j:E(_Jm),k:E(_Jn),l:E(_JC),m:_Iw+_JE|0,n:_JG,o:E(_Ja)+1|0,p:_Jo,q:_Jp,r:E(_Jq),s:_Jr,t:E(_Js),u:E(_Jt),v:E(_Ju),w:(_Iw+_JE|0)<=_JF,x:E(_Jv),y:E(_Jw),z:E(_Jx),A:E(_Jy),B:E(_Jz),C:E(_JA),D:_JB};}else{var _JH=E(_IV);return (!E(_J3))?{_:0,a:E(_Jd),b:E(_Je),c:E(_Jf),d:_Jg,e:_Jh,f:_Ji,g:E(_Jj),h:E(_Jk),i:E(_Jl),j:E(_Jm),k:E(_Jn),l:E(_JC),m:0,n:_JH,o:E(_Ja),p:_Jo,q:_Jp,r:E(_Jq),s:_Jr,t:E(_Js),u:E(_Jt),v:E(_Ju),w:(_Iw+_JE|0)<=_JF,x:E(_Jv),y:E(_Jw),z:E(_Jx),A:E(_Jy),B:E(_Jz),C:E(_JA),D:_JB}:{_:0,a:E(_Jd),b:E(_Je),c:E(_Jf),d:_Jg,e:_Jh,f:_Ji,g:E(_Jj),h:E(_Jk),i:E(_Jl),j:E(_Jm),k:E(_Jn),l:E(_JC),m:0,n:_JH,o:E(_Ja)+1|0,p:_Jo,q:_Jp,r:E(_Jq),s:_Jr,t:E(_Js),u:E(_Jt),v:E(_Ju),w:(_Iw+_JE|0)<=_JF,x:E(_Jv),y:E(_Jw),z:E(_Jx),A:E(_Jy),B:E(_Jz),C:E(_JA),D:_JB};}};if(!E(_IT)){if(!E(_J5)){return B(_JD(1));}else{return B(_JD(B(_7a(_J6,0))+2|0));}}else{return B(_JD(B(_7a(_J4,0))+2|0));}});};if(!E(_IT)){if(!E(_J5)){if(!E(_J3)){var _JI=B(A(_EU,[E(_Ih).a,_IW,_G3,_cl,_IZ,_J0,_IS,_]));return new F(function(){return _Jb(_);});}else{var _JJ=E(_Ih),_JK=_JJ.a,_JL=_JJ.b,_JM=B(_es(_JK,_JL,_J7,_)),_JN=B(_Hs(_JK,_JL,_G6,_IX,new T(function(){return (15+E(_Ja)|0)+1|0;}),_IX,B(_eH(_IP,_Ip)),_));return new F(function(){return _Jb(_);});}}else{var _JO=E(_J7);if(!E(_JO.B)){return new F(function(){return _Jb(_);});}else{var _JP=E(_Ih),_JQ=_JP.a,_JR=_JP.b,_JS=B(_es(_JQ,_JR,_JO,_)),_JT=B(_Hs(_JQ,_JR,_G6,_IX,new T(function(){return 15+E(_Ja)|0;}),_IX,B(_FY(_JO.g,new T(function(){return E(B(_fb(_JO.r)).a);},1),_JO.s)),_));return new F(function(){return _Jb(_);});}}}else{var _JU=new T(function(){if(E(_IX)!=E(_J0)){return E(_IZ);}else{return E(_IZ)+1|0;}}),_JV=new T(function(){var _JW=E(_J0);if(E(_IX)!=_JW){return _JW-1|0;}else{return E(_Fh);}}),_JX=E(_J4);if(!_JX._){return new F(function(){return _Jb(_);});}else{var _JY=E(_Fx);if(!_JY._){return new F(function(){return _Jb(_);});}else{var _JZ=E(_Ih).a,_K0=B(A(_EU,[_JZ,_IW,_H0,_JY.a,_JU,_JV,_JX.a,_])),_K1=function(_K2,_K3,_){while(1){var _K4=E(_K2);if(!_K4._){return _7f;}else{var _K5=E(_K3);if(!_K5._){return _7f;}else{var _K6=B(A(_EU,[_JZ,_IW,_H0,_K5.a,_JU,_JV,_K4.a,_]));_K2=_K4.b;_K3=_K5.b;continue;}}}},_K7=B(_K1(_JX.b,_JY.b,_));return new F(function(){return _Jb(_);});}}}},_K8=E(_IQ);switch(_K8){case 125:return new F(function(){return _IR(32);});break;case 12289:return new F(function(){return _IR(32);});break;case 12290:return new F(function(){return _IR(32);});break;default:return new F(function(){return _IR(_K8);});}}}else{return {_:0,a:E(_Ii),b:E(new T2(0,_Ij,_Ik)),c:E(_Il),d:_Im,e:_In,f:_Io,g:E(_Ip),h:E(_Iq),i:E(_Ir),j:E(_Is),k:E(_It),l:E(_IO),m:_Iw,n:_Ix,o:_Iy,p:_Iz,q:_IA,r:E(_IB),s:_IC,t:E(_ID),u:E(_IE),v:E(_IF),w:E(_ls),x:E(_ls),y:E(_II),z:E(_IJ),A:E(_IK),B:E(_IL),C:E(_IM),D:_IN};}}},_K9=function(_Ka,_Kb,_Kc,_Kd,_Ke,_Kf,_Kg,_Kh,_Ki,_Kj,_Kk,_Kl,_Km,_Kn,_Ko,_Kp,_Kq,_Kr,_Ks,_Kt,_Ku,_Kv,_Kw,_Kx,_Ky,_Kz,_KA,_KB,_KC,_KD,_KE,_KF,_KG,_){while(1){var _KH=B(_Ig(_Ka,_Kb,_Kc,_Kd,_Ke,_Kf,_Kg,_Kh,_Ki,_Kj,_Kk,_Kl,_Km,_Kn,_Ko,_Kp,_Kq,_Kr,_Ks,_Kt,_Ku,_Kv,_Kw,_Kx,_Ky,_Kz,_KA,_KB,_KC,_KD,_KE,_KF,_KG,_)),_KI=E(_KH),_KJ=_KI.a,_KK=_KI.c,_KL=_KI.d,_KM=_KI.e,_KN=_KI.f,_KO=_KI.g,_KP=_KI.h,_KQ=_KI.i,_KR=_KI.j,_KS=_KI.k,_KT=_KI.m,_KU=_KI.n,_KV=_KI.o,_KW=_KI.p,_KX=_KI.q,_KY=_KI.r,_KZ=_KI.s,_L0=_KI.t,_L1=_KI.u,_L2=_KI.v,_L3=_KI.w,_L4=_KI.y,_L5=_KI.A,_L6=_KI.B,_L7=_KI.C,_L8=_KI.D,_L9=E(_KI.b),_La=E(_KI.l);if(!E(_KI.x)){if(!E(_Kz)){return {_:0,a:E(_KJ),b:E(_L9),c:E(_KK),d:_KL,e:_KM,f:_KN,g:E(_KO),h:E(_KP),i:E(_KQ),j:E(_KR),k:E(_KS),l:E(_La),m:_KT,n:_KU,o:_KV,p:_KW,q:_KX,r:E(_KY),s:_KZ,t:E(_L0),u:E(_L1),v:E(_L2),w:E(_L3),x:E(_sd),y:E(_L4),z:E(_sd),A:E(_L5),B:E(_L6),C:E(_L7),D:_L8};}else{_Kb=_KJ;_Kc=_L9.a;_Kd=_L9.b;_Ke=_KK;_Kf=_KL;_Kg=_KM;_Kh=_KN;_Ki=_KO;_Kj=_KP;_Kk=_KQ;_Kl=_KR;_Km=_KS;_Kn=_La.a;_Ko=_La.b;_Kp=_KT;_Kq=_KU;_Kr=_KV;_Ks=_KW;_Kt=_KX;_Ku=_KY;_Kv=_KZ;_Kw=_L0;_Kx=_L1;_Ky=_L2;_Kz=_L3;_KA=_sd;_KB=_L4;_KC=_KI.z;_KD=_L5;_KE=_L6;_KF=_L7;_KG=_L8;continue;}}else{return {_:0,a:E(_KJ),b:E(_L9),c:E(_KK),d:_KL,e:_KM,f:_KN,g:E(_KO),h:E(_KP),i:E(_KQ),j:E(_KR),k:E(_KS),l:E(_La),m:_KT,n:_KU,o:_KV,p:_KW,q:_KX,r:E(_KY),s:_KZ,t:E(_L0),u:E(_L1),v:E(_L2),w:E(_L3),x:E(_ls),y:E(_L4),z:E(_sd),A:E(_L5),B:E(_L6),C:E(_L7),D:_L8};}}},_Lb=function(_Lc,_Ld,_Le,_Lf,_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_){var _LI=B(_Ig(_Lc,_Ld,_Le,_Lf,_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_ls,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_)),_LJ=E(_LI),_LK=_LJ.a,_LL=_LJ.c,_LM=_LJ.d,_LN=_LJ.e,_LO=_LJ.f,_LP=_LJ.g,_LQ=_LJ.h,_LR=_LJ.i,_LS=_LJ.j,_LT=_LJ.k,_LU=_LJ.m,_LV=_LJ.n,_LW=_LJ.o,_LX=_LJ.p,_LY=_LJ.q,_LZ=_LJ.r,_M0=_LJ.s,_M1=_LJ.t,_M2=_LJ.u,_M3=_LJ.v,_M4=_LJ.w,_M5=_LJ.y,_M6=_LJ.A,_M7=_LJ.B,_M8=_LJ.C,_M9=_LJ.D,_Ma=E(_LJ.b),_Mb=E(_LJ.l);if(!E(_LJ.x)){return new F(function(){return _K9(_Lc,_LK,_Ma.a,_Ma.b,_LL,_LM,_LN,_LO,_LP,_LQ,_LR,_LS,_LT,_Mb.a,_Mb.b,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_sd,_M5,_LJ.z,_M6,_M7,_M8,_M9,_);});}else{return {_:0,a:E(_LK),b:E(_Ma),c:E(_LL),d:_LM,e:_LN,f:_LO,g:E(_LP),h:E(_LQ),i:E(_LR),j:E(_LS),k:E(_LT),l:E(_Mb),m:_LU,n:_LV,o:_LW,p:_LX,q:_LY,r:E(_LZ),s:_M0,t:E(_M1),u:E(_M2),v:E(_M3),w:E(_M4),x:E(_ls),y:E(_M5),z:E(_sd),A:E(_M6),B:E(_M7),C:E(_M8),D:_M9};}},_Mc=new T1(0,0),_Md=function(_Me,_Mf){while(1){var _Mg=E(_Me);if(!_Mg._){var _Mh=_Mg.a,_Mi=E(_Mf);if(!_Mi._){return new T1(0,(_Mh>>>0|_Mi.a>>>0)>>>0&4294967295);}else{_Me=new T1(1,I_fromInt(_Mh));_Mf=_Mi;continue;}}else{var _Mj=E(_Mf);if(!_Mj._){_Me=_Mg;_Mf=new T1(1,I_fromInt(_Mj.a));continue;}else{return new T1(1,I_or(_Mg.a,_Mj.a));}}}},_Mk=function(_Ml){var _Mm=E(_Ml);if(!_Mm._){return E(_Mc);}else{return new F(function(){return _Md(new T1(0,E(_Mm.a)),B(_8J(B(_Mk(_Mm.b)),31)));});}},_Mn=function(_Mo,_Mp){if(!E(_Mo)){return new F(function(){return _bo(B(_Mk(_Mp)));});}else{return new F(function(){return _Mk(_Mp);});}},_Mq=1420103680,_Mr=465,_Ms=new T2(1,_Mr,_10),_Mt=new T2(1,_Mq,_Ms),_Mu=new T(function(){return B(_Mn(_ls,_Mt));}),_Mv=function(_Mw){return E(_Mu);},_Mx=0,_My=function(_Mz,_MA){var _MB=_Mz%_MA;if(_Mz<=0){if(_Mz>=0){return E(_MB);}else{if(_MA<=0){return E(_MB);}else{var _MC=E(_MB);return (_MC==0)?0:_MC+_MA|0;}}}else{if(_MA>=0){if(_Mz>=0){return E(_MB);}else{if(_MA<=0){return E(_MB);}else{var _MD=E(_MB);return (_MD==0)?0:_MD+_MA|0;}}}else{var _ME=E(_MB);return (_ME==0)?0:_ME+_MA|0;}}},_MF=function(_MG,_MH){var _MI=E(_MH);switch(_MI){case  -1:return E(_Mx);case 0:return E(_8a);default:return new F(function(){return _My(E(_MG),_MI);});}},_MJ=new T(function(){return B(unCStr("s"));}),_MK=function(_ML,_MM){while(1){var _MN=E(_ML);if(!_MN._){return E(_MM);}else{_ML=_MN.b;_MM=_MN.a;continue;}}},_MO=function(_MP,_MQ,_MR){return new F(function(){return _MK(_MQ,_MP);});},_MS=new T1(0,1),_MT=function(_MU,_MV){var _MW=E(_MU);return new T2(0,_MW,new T(function(){var _MX=B(_MT(B(_8q(_MW,_MV)),_MV));return new T2(1,_MX.a,_MX.b);}));},_MY=function(_MZ){var _N0=B(_MT(_MZ,_MS));return new T2(1,_N0.a,_N0.b);},_N1=function(_N2,_N3){var _N4=B(_MT(_N2,new T(function(){return B(_aJ(_N3,_N2));})));return new T2(1,_N4.a,_N4.b);},_N5=new T1(0,0),_N6=function(_N7,_N8){var _N9=E(_N7);if(!_N9._){var _Na=_N9.a,_Nb=E(_N8);return (_Nb._==0)?_Na>=_Nb.a:I_compareInt(_Nb.a,_Na)<=0;}else{var _Nc=_N9.a,_Nd=E(_N8);return (_Nd._==0)?I_compareInt(_Nc,_Nd.a)>=0:I_compare(_Nc,_Nd.a)>=0;}},_Ne=function(_Nf,_Ng,_Nh){if(!B(_N6(_Ng,_N5))){var _Ni=function(_Nj){return (!B(_92(_Nj,_Nh)))?new T2(1,_Nj,new T(function(){return B(_Ni(B(_8q(_Nj,_Ng))));})):__Z;};return new F(function(){return _Ni(_Nf);});}else{var _Nk=function(_Nl){return (!B(_8T(_Nl,_Nh)))?new T2(1,_Nl,new T(function(){return B(_Nk(B(_8q(_Nl,_Ng))));})):__Z;};return new F(function(){return _Nk(_Nf);});}},_Nm=function(_Nn,_No,_Np){return new F(function(){return _Ne(_Nn,B(_aJ(_No,_Nn)),_Np);});},_Nq=function(_Nr,_Ns){return new F(function(){return _Ne(_Nr,_MS,_Ns);});},_Nt=function(_Nu){return new F(function(){return _8n(_Nu);});},_Nv=function(_Nw){return new F(function(){return _aJ(_Nw,_MS);});},_Nx=function(_Ny){return new F(function(){return _8q(_Ny,_MS);});},_Nz=function(_NA){return new F(function(){return _r0(E(_NA));});},_NB={_:0,a:_Nx,b:_Nv,c:_Nz,d:_Nt,e:_MY,f:_N1,g:_Nq,h:_Nm},_NC=function(_ND,_NE){if(_ND<=0){if(_ND>=0){return new F(function(){return quot(_ND,_NE);});}else{if(_NE<=0){return new F(function(){return quot(_ND,_NE);});}else{return quot(_ND+1|0,_NE)-1|0;}}}else{if(_NE>=0){if(_ND>=0){return new F(function(){return quot(_ND,_NE);});}else{if(_NE<=0){return new F(function(){return quot(_ND,_NE);});}else{return quot(_ND+1|0,_NE)-1|0;}}}else{return quot(_ND-1|0,_NE)-1|0;}}},_NF=function(_NG,_NH){while(1){var _NI=E(_NG);if(!_NI._){var _NJ=E(_NI.a);if(_NJ==( -2147483648)){_NG=new T1(1,I_fromInt( -2147483648));continue;}else{var _NK=E(_NH);if(!_NK._){return new T1(0,B(_NC(_NJ,_NK.a)));}else{_NG=new T1(1,I_fromInt(_NJ));_NH=_NK;continue;}}}else{var _NL=_NI.a,_NM=E(_NH);return (_NM._==0)?new T1(1,I_div(_NL,I_fromInt(_NM.a))):new T1(1,I_div(_NL,_NM.a));}}},_NN=new T1(0,0),_NO=function(_NP,_NQ){if(!B(_8f(_NQ,_NN))){return new F(function(){return _NF(_NP,_NQ);});}else{return E(_8a);}},_NR=function(_NS,_NT){while(1){var _NU=E(_NS);if(!_NU._){var _NV=E(_NU.a);if(_NV==( -2147483648)){_NS=new T1(1,I_fromInt( -2147483648));continue;}else{var _NW=E(_NT);if(!_NW._){var _NX=_NW.a;return new T2(0,new T1(0,B(_NC(_NV,_NX))),new T1(0,B(_My(_NV,_NX))));}else{_NS=new T1(1,I_fromInt(_NV));_NT=_NW;continue;}}}else{var _NY=E(_NT);if(!_NY._){_NS=_NU;_NT=new T1(1,I_fromInt(_NY.a));continue;}else{var _NZ=I_divMod(_NU.a,_NY.a);return new T2(0,new T1(1,_NZ.a),new T1(1,_NZ.b));}}}},_O0=function(_O1,_O2){if(!B(_8f(_O2,_NN))){var _O3=B(_NR(_O1,_O2));return new T2(0,_O3.a,_O3.b);}else{return E(_8a);}},_O4=function(_O5,_O6){while(1){var _O7=E(_O5);if(!_O7._){var _O8=E(_O7.a);if(_O8==( -2147483648)){_O5=new T1(1,I_fromInt( -2147483648));continue;}else{var _O9=E(_O6);if(!_O9._){return new T1(0,B(_My(_O8,_O9.a)));}else{_O5=new T1(1,I_fromInt(_O8));_O6=_O9;continue;}}}else{var _Oa=_O7.a,_Ob=E(_O6);return (_Ob._==0)?new T1(1,I_mod(_Oa,I_fromInt(_Ob.a))):new T1(1,I_mod(_Oa,_Ob.a));}}},_Oc=function(_Od,_Oe){if(!B(_8f(_Oe,_NN))){return new F(function(){return _O4(_Od,_Oe);});}else{return E(_8a);}},_Of=function(_Og,_Oh){while(1){var _Oi=E(_Og);if(!_Oi._){var _Oj=E(_Oi.a);if(_Oj==( -2147483648)){_Og=new T1(1,I_fromInt( -2147483648));continue;}else{var _Ok=E(_Oh);if(!_Ok._){return new T1(0,quot(_Oj,_Ok.a));}else{_Og=new T1(1,I_fromInt(_Oj));_Oh=_Ok;continue;}}}else{var _Ol=_Oi.a,_Om=E(_Oh);return (_Om._==0)?new T1(0,I_toInt(I_quot(_Ol,I_fromInt(_Om.a)))):new T1(1,I_quot(_Ol,_Om.a));}}},_On=function(_Oo,_Op){if(!B(_8f(_Op,_NN))){return new F(function(){return _Of(_Oo,_Op);});}else{return E(_8a);}},_Oq=function(_Or,_Os){if(!B(_8f(_Os,_NN))){var _Ot=B(_8z(_Or,_Os));return new T2(0,_Ot.a,_Ot.b);}else{return E(_8a);}},_Ou=function(_Ov,_Ow){while(1){var _Ox=E(_Ov);if(!_Ox._){var _Oy=E(_Ox.a);if(_Oy==( -2147483648)){_Ov=new T1(1,I_fromInt( -2147483648));continue;}else{var _Oz=E(_Ow);if(!_Oz._){return new T1(0,_Oy%_Oz.a);}else{_Ov=new T1(1,I_fromInt(_Oy));_Ow=_Oz;continue;}}}else{var _OA=_Ox.a,_OB=E(_Ow);return (_OB._==0)?new T1(1,I_rem(_OA,I_fromInt(_OB.a))):new T1(1,I_rem(_OA,_OB.a));}}},_OC=function(_OD,_OE){if(!B(_8f(_OE,_NN))){return new F(function(){return _Ou(_OD,_OE);});}else{return E(_8a);}},_OF=function(_OG){return E(_OG);},_OH=function(_OI){return E(_OI);},_OJ=function(_OK){var _OL=E(_OK);if(!_OL._){var _OM=E(_OL.a);return (_OM==( -2147483648))?E(_bn):(_OM<0)?new T1(0, -_OM):E(_OL);}else{var _ON=_OL.a;return (I_compareInt(_ON,0)>=0)?E(_OL):new T1(1,I_negate(_ON));}},_OO=new T1(0, -1),_OP=function(_OQ){var _OR=E(_OQ);if(!_OR._){var _OS=_OR.a;return (_OS>=0)?(E(_OS)==0)?E(_Mc):E(_91):E(_OO);}else{var _OT=I_compareInt(_OR.a,0);return (_OT<=0)?(E(_OT)==0)?E(_Mc):E(_OO):E(_91);}},_OU={_:0,a:_8q,b:_aJ,c:_r6,d:_bo,e:_OJ,f:_OP,g:_OH},_OV=function(_OW,_OX){var _OY=E(_OW);if(!_OY._){var _OZ=_OY.a,_P0=E(_OX);return (_P0._==0)?_OZ!=_P0.a:(I_compareInt(_P0.a,_OZ)==0)?false:true;}else{var _P1=_OY.a,_P2=E(_OX);return (_P2._==0)?(I_compareInt(_P1,_P2.a)==0)?false:true:(I_compare(_P1,_P2.a)==0)?false:true;}},_P3=new T2(0,_8f,_OV),_P4=function(_P5,_P6){return (!B(_au(_P5,_P6)))?E(_P5):E(_P6);},_P7=function(_P8,_P9){return (!B(_au(_P8,_P9)))?E(_P9):E(_P8);},_Pa={_:0,a:_P3,b:_7q,c:_92,d:_au,e:_8T,f:_N6,g:_P4,h:_P7},_Pb=function(_Pc){return new T2(0,E(_Pc),E(_c7));},_Pd=new T3(0,_OU,_Pa,_Pb),_Pe={_:0,a:_Pd,b:_NB,c:_On,d:_OC,e:_NO,f:_Oc,g:_Oq,h:_O0,i:_OF},_Pf=new T1(0,0),_Pg=function(_Ph,_Pi,_Pj){var _Pk=B(A1(_Ph,_Pi));if(!B(_8f(_Pk,_Pf))){return new F(function(){return _NF(B(_r6(_Pi,_Pj)),_Pk);});}else{return E(_8a);}},_Pl=function(_Pm,_Pn){while(1){if(!B(_8f(_Pn,_NN))){var _Po=_Pn,_Pp=B(_OC(_Pm,_Pn));_Pm=_Po;_Pn=_Pp;continue;}else{return E(_Pm);}}},_Pq=5,_Pr=new T(function(){return B(_86(_Pq));}),_Ps=new T(function(){return die(_Pr);}),_Pt=function(_Pu,_Pv){if(!B(_8f(_Pv,_NN))){var _Pw=B(_Pl(B(_OJ(_Pu)),B(_OJ(_Pv))));return (!B(_8f(_Pw,_NN)))?new T2(0,B(_Of(_Pu,_Pw)),B(_Of(_Pv,_Pw))):E(_8a);}else{return E(_Ps);}},_Px=function(_Py,_Pz,_PA,_PB){var _PC=B(_r6(_Pz,_PA));return new F(function(){return _Pt(B(_r6(B(_r6(_Py,_PB)),B(_OP(_PC)))),B(_OJ(_PC)));});},_PD=function(_PE){return E(E(_PE).a);},_PF=function(_PG){return E(E(_PG).a);},_PH=function(_PI,_PJ,_PK){var _PL=new T(function(){if(!B(_8f(_PK,_NN))){var _PM=B(_8z(_PJ,_PK));return new T2(0,_PM.a,_PM.b);}else{return E(_8a);}}),_PN=new T(function(){return B(A2(_cc,B(_PF(B(_PD(_PI)))),new T(function(){return E(E(_PL).a);})));});return new T2(0,_PN,new T(function(){return new T2(0,E(E(_PL).b),E(_PK));}));},_PO=function(_PP,_PQ,_PR){var _PS=B(_PH(_PP,_PQ,_PR)),_PT=_PS.a,_PU=E(_PS.b);if(!B(_92(B(_r6(_PU.a,_c7)),B(_r6(_NN,_PU.b))))){return E(_PT);}else{var _PV=B(_PF(B(_PD(_PP))));return new F(function(){return A3(_Fl,_PV,_PT,new T(function(){return B(A2(_cc,_PV,_c7));}));});}},_PW=479723520,_PX=40233135,_PY=new T2(1,_PX,_10),_PZ=new T2(1,_PW,_PY),_Q0=new T(function(){return B(_Mn(_ls,_PZ));}),_Q1=new T1(0,40587),_Q2=function(_Q3){var _Q4=new T(function(){var _Q5=B(_Px(_Q3,_c7,_Mu,_c7)),_Q6=B(_Px(_Q0,_c7,_Mu,_c7)),_Q7=B(_Px(_Q5.a,_Q5.b,_Q6.a,_Q6.b));return B(_PO(_Pe,_Q7.a,_Q7.b));});return new T2(0,new T(function(){return B(_8q(_Q1,_Q4));}),new T(function(){return B(_aJ(_Q3,B(_Pg(_Mv,B(_r6(_Q4,_Mu)),_Q0))));}));},_Q8=function(_Q9,_){var _Qa=__get(_Q9,0),_Qb=__get(_Q9,1),_Qc=Number(_Qa),_Qd=jsTrunc(_Qc),_Qe=Number(_Qb),_Qf=jsTrunc(_Qe);return new T2(0,_Qd,_Qf);},_Qg=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_Qh=660865024,_Qi=465661287,_Qj=new T2(1,_Qi,_10),_Qk=new T2(1,_Qh,_Qj),_Ql=new T(function(){return B(_Mn(_ls,_Qk));}),_Qm=function(_){var _Qn=__app0(E(_Qg)),_Qo=B(_Q8(_Qn,_));return new T(function(){var _Qp=E(_Qo);if(!B(_8f(_Ql,_Pf))){return B(_8q(B(_r6(B(_r0(E(_Qp.a))),_Mu)),B(_NF(B(_r6(B(_r6(B(_r0(E(_Qp.b))),_Mu)),_Mu)),_Ql))));}else{return E(_8a);}});},_Qq=new T(function(){return B(err(_nZ));}),_Qr=new T(function(){return B(err(_nX));}),_Qs=new T(function(){return B(A3(_zS,_Al,_zn,_As));}),_Qt=new T1(0,1),_Qu=new T1(0,10),_Qv=function(_Qw){while(1){var _Qx=E(_Qw);if(!_Qx._){_Qw=new T1(1,I_fromInt(_Qx.a));continue;}else{return new F(function(){return I_toString(_Qx.a);});}}},_Qy=function(_Qz,_QA){return new F(function(){return _y(fromJSStr(B(_Qv(_Qz))),_QA);});},_QB=new T1(0,0),_QC=function(_QD,_QE,_QF){if(_QD<=6){return new F(function(){return _Qy(_QE,_QF);});}else{if(!B(_92(_QE,_QB))){return new F(function(){return _Qy(_QE,_QF);});}else{return new T2(1,_H,new T(function(){return B(_y(fromJSStr(B(_Qv(_QE))),new T2(1,_G,_QF)));}));}}},_QG=function(_QH,_QI,_QJ){while(1){if(!(_QI%2)){var _QK=B(_r6(_QH,_QH)),_QL=quot(_QI,2);_QH=_QK;_QI=_QL;continue;}else{var _QM=E(_QI);if(_QM==1){return new F(function(){return _r6(_QH,_QJ);});}else{var _QK=B(_r6(_QH,_QH)),_QN=B(_r6(_QH,_QJ));_QH=_QK;_QI=quot(_QM-1|0,2);_QJ=_QN;continue;}}}},_QO=function(_QP,_QQ){while(1){if(!(_QQ%2)){var _QR=B(_r6(_QP,_QP)),_QS=quot(_QQ,2);_QP=_QR;_QQ=_QS;continue;}else{var _QT=E(_QQ);if(_QT==1){return E(_QP);}else{return new F(function(){return _QG(B(_r6(_QP,_QP)),quot(_QT-1|0,2),_QP);});}}}},_QU=new T(function(){return B(unCStr("Negative exponent"));}),_QV=new T(function(){return B(err(_QU));}),_QW=function(_QX){return new F(function(){return _QC(0,_QX,_10);});},_QY=new T(function(){return B(_8f(_Qu,_Pf));}),_QZ=function(_R0){while(1){if(!B(_8f(_R0,_Pf))){if(!E(_QY)){if(!B(_8f(B(_O4(_R0,_Qu)),_Pf))){return new F(function(){return _QW(_R0);});}else{var _R1=B(_NF(_R0,_Qu));_R0=_R1;continue;}}else{return E(_8a);}}else{return __Z;}}},_R2=46,_R3=48,_R4=function(_R5,_R6,_R7){if(!B(_92(_R7,_Pf))){var _R8=B(A1(_R5,_R7));if(!B(_8f(_R8,_Pf))){var _R9=B(_NR(_R7,_R8)),_Ra=_R9.b,_Rb=new T(function(){var _Rc=Math.log(B(_bH(_R8)))/Math.log(10),_Rd=_Rc&4294967295,_Re=function(_Rf){if(_Rf>=0){var _Rg=E(_Rf);if(!_Rg){var _Rh=B(_NF(B(_aJ(B(_8q(B(_r6(_Ra,_c7)),_R8)),_Qt)),_R8));}else{var _Rh=B(_NF(B(_aJ(B(_8q(B(_r6(_Ra,B(_QO(_Qu,_Rg)))),_R8)),_Qt)),_R8));}var _Ri=function(_Rj){var _Rk=B(_QC(0,_Rh,_10)),_Rl=_Rf-B(_7a(_Rk,0))|0;if(0>=_Rl){if(!E(_R6)){return E(_Rk);}else{return new F(function(){return _QZ(_Rh);});}}else{var _Rm=new T(function(){if(!E(_R6)){return E(_Rk);}else{return B(_QZ(_Rh));}}),_Rn=function(_Ro){var _Rp=E(_Ro);return (_Rp==1)?E(new T2(1,_R3,_Rm)):new T2(1,_R3,new T(function(){return B(_Rn(_Rp-1|0));}));};return new F(function(){return _Rn(_Rl);});}};if(!E(_R6)){var _Rq=B(_Ri(_));return (_Rq._==0)?__Z:new T2(1,_R2,_Rq);}else{if(!B(_8f(_Rh,_Pf))){var _Rr=B(_Ri(_));return (_Rr._==0)?__Z:new T2(1,_R2,_Rr);}else{return __Z;}}}else{return E(_QV);}};if(_Rd>=_Rc){return B(_Re(_Rd));}else{return B(_Re(_Rd+1|0));}},1);return new F(function(){return _y(B(_QC(0,_R9.a,_10)),_Rb);});}else{return E(_8a);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_R4(_R5,_R6,B(_bo(_R7))));}));});}},_Rs=function(_Rt,_Ru,_){var _Rv=B(_Qm(_)),_Rw=new T(function(){var _Rx=new T(function(){var _Ry=new T(function(){var _Rz=B(_y(B(_R4(_Mv,_ls,B(_Q2(_Rv)).b)),_MJ));if(!_Rz._){return E(_D2);}else{var _RA=B(_CX(_Rz.a,_Rz.b));if(!_RA._){return B(_MO(_10,_10,_Fg));}else{var _RB=_RA.a,_RC=E(_RA.b);if(!_RC._){return B(_MO(new T2(1,_RB,_10),_10,_Fg));}else{var _RD=E(_RB),_RE=new T(function(){var _RF=B(_lz(46,_RC.a,_RC.b));return new T2(0,_RF.a,_RF.b);});if(E(_RD)==46){return B(_MO(_10,new T2(1,new T(function(){return E(E(_RE).a);}),new T(function(){return E(E(_RE).b);})),_Fg));}else{return B(_MO(new T2(1,_RD,new T(function(){return E(E(_RE).a);})),new T(function(){return E(E(_RE).b);}),_Fg));}}}}}),_RG=B(_Az(B(_o8(_Qs,_Ry))));if(!_RG._){return E(_Qr);}else{if(!E(_RG.b)._){return B(_eH(3,B(_I(0,E(_RG.a)+(imul(E(_Ru),E(_Rt)-1|0)|0)|0,_10))));}else{return E(_Qq);}}}),_RH=B(_Az(B(_o8(_Qs,_Rx))));if(!_RH._){return E(_Qr);}else{if(!E(_RH.b)._){return E(_RH.a);}else{return E(_Qq);}}});return new T2(0,new T(function(){return B(_MF(_Rw,_Rt));}),_Rw);},_RI=function(_RJ){var _RK=E(_RJ);if(!_RK._){return new T2(0,_10,_10);}else{var _RL=E(_RK.a),_RM=new T(function(){var _RN=B(_RI(_RK.b));return new T2(0,_RN.a,_RN.b);});return new T2(0,new T2(1,_RL.a,new T(function(){return E(E(_RM).a);})),new T2(1,_RL.b,new T(function(){return E(E(_RM).b);})));}},_RO=function(_RP){return new F(function(){return _lu("Check.hs:66:21-47|(l : r : _)");});},_RQ=new T(function(){return B(_RO(_));}),_RR=61,_RS=function(_RT,_RU){while(1){var _RV=E(_RT);if(!_RV._){return E(_RU);}else{_RT=_RV.b;_RU=_RV.a;continue;}}},_RW=function(_RX,_RY,_RZ){return new F(function(){return _RS(_RY,_RX);});},_S0=function(_S1,_S2){var _S3=E(_S2);if(!_S3._){return new T2(0,_10,_10);}else{var _S4=_S3.a;if(!B(A1(_S1,_S4))){var _S5=new T(function(){var _S6=B(_S0(_S1,_S3.b));return new T2(0,_S6.a,_S6.b);});return new T2(0,new T2(1,_S4,new T(function(){return E(E(_S5).a);})),new T(function(){return E(E(_S5).b);}));}else{return new T2(0,_10,_S3);}}},_S7=function(_S8,_S9){while(1){var _Sa=E(_S9);if(!_Sa._){return __Z;}else{if(!B(A1(_S8,_Sa.a))){return E(_Sa);}else{_S9=_Sa.b;continue;}}}},_Sb=function(_Sc){var _Sd=_Sc>>>0;if(_Sd>887){var _Se=u_iswspace(_Sc);return (E(_Se)==0)?false:true;}else{var _Sf=E(_Sd);return (_Sf==32)?true:(_Sf-9>>>0>4)?(E(_Sf)==160)?true:false:true;}},_Sg=function(_Sh){return new F(function(){return _Sb(E(_Sh));});},_Si=function(_Sj){var _Sk=B(_S7(_Sg,_Sj));if(!_Sk._){return __Z;}else{var _Sl=new T(function(){var _Sm=B(_S0(_Sg,_Sk));return new T2(0,_Sm.a,_Sm.b);});return new T2(1,new T(function(){return E(E(_Sl).a);}),new T(function(){return B(_Si(E(_Sl).b));}));}},_Sn=function(_So){if(!B(_4B(_6f,_RR,_So))){return new T2(0,_So,_10);}else{var _Sp=new T(function(){var _Sq=E(_So);if(!_Sq._){return E(_RQ);}else{var _Sr=E(_Sq.b);if(!_Sr._){return E(_RQ);}else{var _Ss=_Sr.a,_St=_Sr.b,_Su=E(_Sq.a);if(E(_Su)==61){return new T2(0,_10,new T(function(){return E(B(_lz(61,_Ss,_St)).a);}));}else{var _Sv=B(_lz(61,_Ss,_St)),_Sw=E(_Sv.b);if(!_Sw._){return E(_RQ);}else{return new T2(0,new T2(1,_Su,_Sv.a),_Sw.a);}}}}});return new T2(0,new T(function(){var _Sx=B(_Si(E(_Sp).a));if(!_Sx._){return __Z;}else{return B(_RW(_Sx.a,_Sx.b,_Fg));}}),new T(function(){var _Sy=B(_Si(E(_Sp).b));if(!_Sy._){return __Z;}else{return E(_Sy.a);}}));}},_Sz=new T(function(){return B(unCStr("+-*^"));}),_SA=new T(function(){return B(unCStr("0123456789"));}),_SB=new T(function(){return B(_lu("Siki.hs:12:9-28|(hn : ns, cs)"));}),_SC=new T2(1,_10,_10),_SD=function(_SE){var _SF=E(_SE);if(!_SF._){return new T2(0,_SC,_10);}else{var _SG=_SF.a,_SH=new T(function(){var _SI=B(_SD(_SF.b)),_SJ=E(_SI.a);if(!_SJ._){return E(_SB);}else{return new T3(0,_SJ.a,_SJ.b,_SI.b);}});return (!B(_4B(_6f,_SG,_SA)))?(!B(_4B(_6f,_SG,_Sz)))?new T2(0,new T2(1,new T2(1,_SG,new T(function(){return E(E(_SH).a);})),new T(function(){return E(E(_SH).b);})),new T(function(){return E(E(_SH).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_SH).a);}),new T(function(){return E(E(_SH).b);}))),new T2(1,_SG,new T(function(){return E(E(_SH).c);}))):new T2(0,new T2(1,new T2(1,_SG,new T(function(){return E(E(_SH).a);})),new T(function(){return E(E(_SH).b);})),new T(function(){return E(E(_SH).c);}));}},_SK=function(_SL,_SM){while(1){var _SN=E(_SM);if(!_SN._){return __Z;}else{var _SO=_SN.b,_SP=E(_SL);if(_SP==1){return E(_SO);}else{_SL=_SP-1|0;_SM=_SO;continue;}}}},_SQ=function(_SR,_SS){while(1){var _ST=E(_SS);if(!_ST._){return __Z;}else{var _SU=_ST.b,_SV=E(_SR);if(_SV==1){return E(_SU);}else{_SR=_SV-1|0;_SS=_SU;continue;}}}},_SW=function(_SX,_SY){while(1){var _SZ=E(_SX);if(!_SZ._){return E(_SY);}else{var _T0=new T2(1,_SZ.a,_SY);_SX=_SZ.b;_SY=_T0;continue;}}},_T1=function(_T2){return new F(function(){return _SW(_T2,_10);});},_T3=function(_T4,_T5,_T6,_T7){var _T8=new T(function(){return B(_jf(_6f,_T5,_T6));}),_T9=new T(function(){var _Ta=E(_T8),_Tb=new T(function(){var _Tc=_Ta+1|0;if(_Tc>0){return B(_SQ(_Tc,_T6));}else{return E(_T6);}});if(0>=_Ta){return E(_Tb);}else{var _Td=function(_Te,_Tf){var _Tg=E(_Te);if(!_Tg._){return E(_Tb);}else{var _Th=_Tg.a,_Ti=E(_Tf);return (_Ti==1)?new T2(1,_Th,_Tb):new T2(1,_Th,new T(function(){return B(_Td(_Tg.b,_Ti-1|0));}));}};return B(_Td(_T6,_Ta));}}),_Tj=new T(function(){var _Tk=E(_T8),_Tl=new T(function(){if(E(_T5)==94){return B(A2(_T4,new T(function(){return B(_77(_T7,_Tk+1|0));}),new T(function(){return B(_77(_T7,_Tk));})));}else{return B(A2(_T4,new T(function(){return B(_77(_T7,_Tk));}),new T(function(){return B(_77(_T7,_Tk+1|0));})));}}),_Tm=new T2(1,_Tl,new T(function(){var _Tn=_Tk+2|0;if(_Tn>0){return B(_SK(_Tn,_T7));}else{return E(_T7);}}));if(0>=_Tk){return E(_Tm);}else{var _To=function(_Tp,_Tq){var _Tr=E(_Tp);if(!_Tr._){return E(_Tm);}else{var _Ts=_Tr.a,_Tt=E(_Tq);return (_Tt==1)?new T2(1,_Ts,_Tm):new T2(1,_Ts,new T(function(){return B(_To(_Tr.b,_Tt-1|0));}));}};return B(_To(_T7,_Tk));}});return (E(_T5)==94)?new T2(0,new T(function(){return B(_T1(_T9));}),new T(function(){return B(_T1(_Tj));})):new T2(0,_T9,_Tj);},_Tu=new T1(0,2),_Tv=new T(function(){return B(_8f(_Tu,_NN));}),_Tw=function(_Tx,_Ty,_Tz){while(1){if(!E(_Tv)){if(!B(_8f(B(_Ou(_Ty,_Tu)),_NN))){if(!B(_8f(_Ty,_c7))){var _TA=B(_r6(_Tx,_Tx)),_TB=B(_Of(B(_aJ(_Ty,_c7)),_Tu)),_TC=B(_r6(_Tx,_Tz));_Tx=_TA;_Ty=_TB;_Tz=_TC;continue;}else{return new F(function(){return _r6(_Tx,_Tz);});}}else{var _TA=B(_r6(_Tx,_Tx)),_TB=B(_Of(_Ty,_Tu));_Tx=_TA;_Ty=_TB;continue;}}else{return E(_8a);}}},_TD=function(_TE,_TF){while(1){if(!E(_Tv)){if(!B(_8f(B(_Ou(_TF,_Tu)),_NN))){if(!B(_8f(_TF,_c7))){return new F(function(){return _Tw(B(_r6(_TE,_TE)),B(_Of(B(_aJ(_TF,_c7)),_Tu)),_TE);});}else{return E(_TE);}}else{var _TG=B(_r6(_TE,_TE)),_TH=B(_Of(_TF,_Tu));_TE=_TG;_TF=_TH;continue;}}else{return E(_8a);}}},_TI=function(_TJ,_TK){if(!B(_92(_TK,_NN))){if(!B(_8f(_TK,_NN))){return new F(function(){return _TD(_TJ,_TK);});}else{return E(_c7);}}else{return E(_QV);}},_TL=94,_TM=45,_TN=43,_TO=42,_TP=function(_TQ,_TR){while(1){var _TS=B((function(_TT,_TU){var _TV=E(_TU);if(!_TV._){return __Z;}else{if((B(_7a(_TT,0))+1|0)==B(_7a(_TV,0))){if(!B(_4B(_6f,_TL,_TT))){if(!B(_4B(_6f,_TO,_TT))){if(!B(_4B(_6f,_TN,_TT))){if(!B(_4B(_6f,_TM,_TT))){return E(_TV);}else{var _TW=B(_T3(_aJ,45,_TT,_TV));_TQ=_TW.a;_TR=_TW.b;return __continue;}}else{var _TX=B(_T3(_8q,43,_TT,_TV));_TQ=_TX.a;_TR=_TX.b;return __continue;}}else{var _TY=B(_T3(_r6,42,_TT,_TV));_TQ=_TY.a;_TR=_TY.b;return __continue;}}else{var _TZ=B(_T3(_TI,94,new T(function(){return B(_T1(_TT));}),new T(function(){return B(_SW(_TV,_10));})));_TQ=_TZ.a;_TR=_TZ.b;return __continue;}}else{return __Z;}}})(_TQ,_TR));if(_TS!=__continue){return _TS;}}},_U0=function(_U1){var _U2=E(_U1);if(!_U2._){return new T2(0,_10,_10);}else{var _U3=E(_U2.a),_U4=new T(function(){var _U5=B(_U0(_U2.b));return new T2(0,_U5.a,_U5.b);});return new T2(0,new T2(1,_U3.a,new T(function(){return E(E(_U4).a);})),new T2(1,_U3.b,new T(function(){return E(E(_U4).b);})));}},_U6=new T(function(){return B(unCStr("0123456789+-"));}),_U7=function(_U8){while(1){var _U9=E(_U8);if(!_U9._){return true;}else{if(!B(_4B(_6f,_U9.a,_U6))){return false;}else{_U8=_U9.b;continue;}}}},_Ua=new T(function(){return B(err(_nX));}),_Ub=new T(function(){return B(err(_nZ));}),_Uc=function(_Ud,_Ue){var _Uf=function(_Ug,_Uh){var _Ui=function(_Uj){return new F(function(){return A1(_Uh,new T(function(){return B(_bo(_Uj));}));});},_Uk=new T(function(){return B(_yQ(function(_Ul){return new F(function(){return A3(_Ud,_Ul,_Ug,_Ui);});}));}),_Um=function(_Un){return E(_Uk);},_Uo=function(_Up){return new F(function(){return A2(_xx,_Up,_Um);});},_Uq=new T(function(){return B(_yQ(function(_Ur){var _Us=E(_Ur);if(_Us._==4){var _Ut=E(_Us.a);if(!_Ut._){return new F(function(){return A3(_Ud,_Us,_Ug,_Uh);});}else{if(E(_Ut.a)==45){if(!E(_Ut.b)._){return E(new T1(1,_Uo));}else{return new F(function(){return A3(_Ud,_Us,_Ug,_Uh);});}}else{return new F(function(){return A3(_Ud,_Us,_Ug,_Uh);});}}}else{return new F(function(){return A3(_Ud,_Us,_Ug,_Uh);});}}));}),_Uu=function(_Uv){return E(_Uq);};return new T1(1,function(_Uw){return new F(function(){return A2(_xx,_Uw,_Uu);});});};return new F(function(){return _zH(_Uf,_Ue);});},_Ux=function(_Uy){var _Uz=E(_Uy);if(_Uz._==5){var _UA=B(_Ad(_Uz.a));return (_UA._==0)?E(_Ai):function(_UB,_UC){return new F(function(){return A1(_UC,_UA.a);});};}else{return E(_Ai);}},_UD=new T(function(){return B(A3(_Uc,_Ux,_zn,_As));}),_UE=function(_UF,_UG){var _UH=E(_UG);if(!_UH._){return __Z;}else{var _UI=_UH.a,_UJ=_UH.b,_UK=function(_UL){var _UM=B(_U0(_UF)),_UN=_UM.a;return (!B(_4B(_fp,_UI,_UN)))?__Z:new T2(1,new T(function(){return B(_77(_UM.b,B(_jf(_fp,_UI,_UN))));}),new T(function(){return B(_UE(_UF,_UJ));}));};if(!B(_fh(_UI,_10))){if(!B(_U7(_UI))){return new F(function(){return _UK(_);});}else{return new T2(1,new T(function(){var _UO=B(_Az(B(_o8(_UD,_UI))));if(!_UO._){return E(_Ua);}else{if(!E(_UO.b)._){return E(_UO.a);}else{return E(_Ub);}}}),new T(function(){return B(_UE(_UF,_UJ));}));}}else{return new F(function(){return _UK(_);});}}},_UP=function(_UQ,_UR){while(1){var _US=E(_UQ);if(!_US._){return E(_UR);}else{_UQ=_US.b;_UR=_US.a;continue;}}},_UT=function(_UU,_UV,_UW){return new F(function(){return _UP(_UV,_UU);});},_UX=function(_UY,_UZ){var _V0=B(_SD(_UZ)),_V1=B(_TP(_V0.b,B(_UE(_UY,_V0.a))));if(!_V1._){return E(_UZ);}else{return new F(function(){return _QC(0,B(_UT(_V1.a,_V1.b,_Fg)),_10);});}},_V2=function(_V3,_V4){var _V5=function(_V6,_V7){while(1){var _V8=B((function(_V9,_Va){var _Vb=E(_Va);if(!_Vb._){return (!B(_hq(_V9,_10)))?new T2(0,_ls,_V9):new T2(0,_sd,_10);}else{var _Vc=_Vb.b,_Vd=B(_RI(_Vb.a)).a;if(!B(_4B(_6f,_RR,_Vd))){var _Ve=_V9;_V6=_Ve;_V7=_Vc;return __continue;}else{var _Vf=B(_Sn(_Vd)),_Vg=_Vf.a,_Vh=_Vf.b;if(!B(_hq(B(_UX(_V3,_Vg)),B(_UX(_V3,_Vh))))){return new T2(0,_sd,_10);}else{if(!B(_fh(_Vh,_10))){var _Vi=new T(function(){if(!B(_hq(_V9,_10))){return B(_y(_V9,new T(function(){return B(unAppCStr(" ",_Vg));},1)));}else{return E(_Vg);}});_V6=_Vi;_V7=_Vc;return __continue;}else{return new T2(0,_sd,_10);}}}}})(_V6,_V7));if(_V8!=__continue){return _V8;}}};return new F(function(){return _V5(_10,_V4);});},_Vj=function(_Vk,_Vl){while(1){var _Vm=E(_Vk);if(!_Vm._){return E(_Vl);}else{_Vk=_Vm.b;_Vl=_Vm.a;continue;}}},_Vn=function(_Vo,_Vp,_Vq){return new F(function(){return _Vj(_Vp,_Vo);});},_Vr=function(_Vs,_Vt){while(1){var _Vu=E(_Vs);if(!_Vu._){return E(_Vt);}else{_Vs=_Vu.b;_Vt=_Vu.a;continue;}}},_Vv=function(_Vw,_Vx,_Vy){return new F(function(){return _Vr(_Vx,_Vw);});},_Vz=function(_VA,_VB){while(1){var _VC=E(_VB);if(!_VC._){return __Z;}else{var _VD=_VC.b,_VE=E(_VA);if(_VE==1){return E(_VD);}else{_VA=_VE-1|0;_VB=_VD;continue;}}}},_VF=function(_VG,_VH){var _VI=new T(function(){var _VJ=_VG+1|0;if(_VJ>0){return B(_Vz(_VJ,_VH));}else{return E(_VH);}});if(0>=_VG){return E(_VI);}else{var _VK=function(_VL,_VM){var _VN=E(_VL);if(!_VN._){return E(_VI);}else{var _VO=_VN.a,_VP=E(_VM);return (_VP==1)?new T2(1,_VO,_VI):new T2(1,_VO,new T(function(){return B(_VK(_VN.b,_VP-1|0));}));}};return new F(function(){return _VK(_VH,_VG);});}},_VQ=new T(function(){return B(A3(_zS,_Al,_zn,_As));}),_VR=new T(function(){return B(unCStr("!"));}),_VS=0,_VT=function(_VU){return new F(function(){return _lu("Check.hs:154:7-35|(co : na : xs)");});},_VV=new T(function(){return B(_VT(_));}),_VW=new T(function(){return B(err(_nZ));}),_VX=new T(function(){return B(err(_nX));}),_VY=new T(function(){return B(unCStr(":"));}),_VZ=function(_W0){var _W1=E(_W0);if(!_W1._){return __Z;}else{var _W2=new T(function(){return B(_y(_VY,new T(function(){return B(_VZ(_W1.b));},1)));},1);return new F(function(){return _y(_W1.a,_W2);});}},_W3=function(_W4,_W5){var _W6=new T(function(){return B(_y(_VY,new T(function(){return B(_VZ(_W5));},1)));},1);return new F(function(){return _y(_W4,_W6);});},_W7=function(_W8,_W9){var _Wa=E(_W9);if(!_Wa._){return E(_VV);}else{var _Wb=E(_Wa.b);if(!_Wb._){return E(_VV);}else{var _Wc=E(_Wa.a),_Wd=new T(function(){var _We=B(_lz(58,_Wb.a,_Wb.b));return new T2(0,_We.a,_We.b);}),_Wf=function(_Wg,_Wh,_Wi){var _Wj=function(_Wk){if((_W8+1|0)!=_Wk){return new T3(0,_W8+1|0,_Wh,_Wa);}else{var _Wl=E(_Wi);return (_Wl._==0)?new T3(0,_VS,_Wh,_10):new T3(0,_VS,_Wh,new T(function(){var _Wm=B(_W3(_Wl.a,_Wl.b));if(!_Wm._){return E(_D2);}else{return B(_CX(_Wm.a,_Wm.b));}}));}};if(!B(_hq(_Wg,_VR))){var _Wn=B(_Az(B(_o8(_VQ,_Wg))));if(!_Wn._){return E(_VX);}else{if(!E(_Wn.b)._){return new F(function(){return _Wj(E(_Wn.a));});}else{return E(_VW);}}}else{return new F(function(){return _Wj( -1);});}};if(E(_Wc)==58){return new F(function(){return _Wf(_10,new T(function(){return E(E(_Wd).a);}),new T(function(){return E(E(_Wd).b);}));});}else{var _Wo=E(_Wd),_Wp=E(_Wo.b);if(!_Wp._){return E(_VV);}else{return new F(function(){return _Wf(new T2(1,_Wc,_Wo.a),_Wp.a,_Wp.b);});}}}}},_Wq=function(_Wr,_Ws){while(1){var _Wt=E(_Ws);if(!_Wt._){return __Z;}else{var _Wu=_Wt.b,_Wv=E(_Wr);if(_Wv==1){return E(_Wu);}else{_Wr=_Wv-1|0;_Ws=_Wu;continue;}}}},_Ww=function(_Wx,_Wy,_Wz){var _WA=new T2(1,_Wy,new T(function(){var _WB=_Wx+1|0;if(_WB>0){return B(_Wq(_WB,_Wz));}else{return E(_Wz);}}));if(0>=_Wx){return E(_WA);}else{var _WC=function(_WD,_WE){var _WF=E(_WD);if(!_WF._){return E(_WA);}else{var _WG=_WF.a,_WH=E(_WE);return (_WH==1)?new T2(1,_WG,_WA):new T2(1,_WG,new T(function(){return B(_WC(_WF.b,_WH-1|0));}));}};return new F(function(){return _WC(_Wz,_Wx);});}},_WI=function(_WJ,_WK){if(_WJ<=_WK){var _WL=function(_WM){return new T2(1,_WM,new T(function(){if(_WM!=_WK){return B(_WL(_WM+1|0));}else{return __Z;}}));};return new F(function(){return _WL(_WJ);});}else{return __Z;}},_WN=new T2(0,_CF,_CD),_WO=function(_WP,_WQ,_WR){while(1){var _WS=E(_WR);if(!_WS._){return E(_WN);}else{var _WT=_WS.b,_WU=E(_WS.a),_WV=E(_WU.a);if(_WP!=E(_WV.a)){_WR=_WT;continue;}else{if(_WQ!=E(_WV.b)){_WR=_WT;continue;}else{return E(_WU.b);}}}}},_WW=function(_WX,_WY){while(1){var _WZ=E(_WY);if(!_WZ._){return __Z;}else{var _X0=_WZ.b,_X1=E(_WX);if(_X1==1){return E(_X0);}else{_WX=_X1-1|0;_WY=_X0;continue;}}}},_X2=function(_X3,_X4,_X5){var _X6=E(_X3);if(_X6==1){return E(_X5);}else{return new F(function(){return _WW(_X6-1|0,_X5);});}},_X7=function(_X8,_X9,_Xa){return new T2(1,new T(function(){if(0>=_X8){return __Z;}else{return B(_eH(_X8,new T2(1,_X9,_Xa)));}}),new T(function(){if(_X8>0){return B(_Xb(_X8,B(_X2(_X8,_X9,_Xa))));}else{return B(_X7(_X8,_X9,_Xa));}}));},_Xb=function(_Xc,_Xd){var _Xe=E(_Xd);if(!_Xe._){return __Z;}else{var _Xf=_Xe.a,_Xg=_Xe.b;return new T2(1,new T(function(){if(0>=_Xc){return __Z;}else{return B(_eH(_Xc,_Xe));}}),new T(function(){if(_Xc>0){return B(_Xb(_Xc,B(_X2(_Xc,_Xf,_Xg))));}else{return B(_X7(_Xc,_Xf,_Xg));}}));}},_Xh=function(_Xi,_Xj,_Xk){var _Xl=_Xj-1|0;if(0<=_Xl){var _Xm=E(_Xi),_Xn=function(_Xo){var _Xp=new T(function(){if(_Xo!=_Xl){return B(_Xn(_Xo+1|0));}else{return __Z;}}),_Xq=function(_Xr){var _Xs=E(_Xr);return (_Xs._==0)?E(_Xp):new T2(1,new T(function(){var _Xt=E(_Xk);if(!_Xt._){return E(_WN);}else{var _Xu=_Xt.b,_Xv=E(_Xt.a),_Xw=E(_Xv.a),_Xx=E(_Xs.a);if(_Xx!=E(_Xw.a)){return B(_WO(_Xx,_Xo,_Xu));}else{if(_Xo!=E(_Xw.b)){return B(_WO(_Xx,_Xo,_Xu));}else{return E(_Xv.b);}}}}),new T(function(){return B(_Xq(_Xs.b));}));};return new F(function(){return _Xq(B(_WI(0,_Xm-1|0)));});};return new F(function(){return _Xb(_Xm,B(_Xn(0)));});}else{return __Z;}},_Xy=function(_Xz,_XA){while(1){var _XB=E(_XA);if(!_XB._){return __Z;}else{var _XC=_XB.b,_XD=E(_Xz);if(_XD==1){return E(_XC);}else{_Xz=_XD-1|0;_XA=_XC;continue;}}}},_XE=function(_XF){var _XG=E(_XF);if(!_XG._){return new T2(0,_10,_10);}else{var _XH=E(_XG.a),_XI=new T(function(){var _XJ=B(_XE(_XG.b));return new T2(0,_XJ.a,_XJ.b);});return new T2(0,new T2(1,_XH.a,new T(function(){return E(E(_XI).a);})),new T2(1,_XH.b,new T(function(){return E(E(_XI).b);})));}},_XK=function(_XL,_XM,_XN){var _XO=new T(function(){var _XP=B(_XE(_XN));return new T2(0,_XP.a,_XP.b);});return new T2(0,new T2(1,_XL,new T(function(){return E(E(_XO).a);})),new T2(1,_XM,new T(function(){return E(E(_XO).b);})));},_XQ=new T(function(){return B(unCStr("\u4e0d\u601d\u8b70\u306a\u3068\u3053\u308d\u30fb\u30fb\u30fb\u3002\n\u3053\u3053\u306f \u3069\u3053\u3060\u3089\u3046\u30fb\u30fb\u30fb\u3002\n\uff1c\u30ad\u30fc\u30dc\u30fc\u30c9\u306a\u3089 hjkl\u30ad\u30fc\u3092\u3002\n\u30bf\u30c3\u30c1\u306a\u3089 \u753b\u9762\u306e\u7aef\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3053\u3068\u3067 \u52d5\u3051\u3055\u3046\u3067\u3059\uff1e{e.bC.m1:s0C0:1:s0C1:1:s0C2:0:s0C3}{e.==.m1:s0c}{e.b9.m1:s090}{e.b8.m1:s080}{e.b3.m1:s030}{e.b2.m1:s020}"));}),_XR=new T(function(){return B(unCStr("s0C0"));}),_XS=new T(function(){return B(unCStr("\n\u300c\u3084\u3042\u3002\n\u308f\u3042\uff01 \u306a\u3093\u304b\u6587\u5b57\u304c\u3057\u3083\u3079\u3063\u305f\uff01\u3002\n\u300c\u6587\u5b57\u3062\u3083\u306a\u3044\u3088\u3002\n\u300c\u50d5\u306f \u306d\u3053\u3060\u3088\u3002\n\u3044\u3084 \u306d\u3053\u3082 \u666e\u901a\u3057\u3083\u3079\u3089\u306a\u3044\u3057\u3002\n\u300c\u3069\u3046\u3060\u3044\uff1f \u6b21\u306b\u9032\u3081\u3055\u3046\u304b\u3044\uff1f\u3002\n\u6b21\u3063\u3066\u3044\u3063\u3066\u3082 \u3088\u304f\u308f\u304b\u3089\u306a\u3044\u3051\u3069\u30fb\u30fb\u30fb\u3002\n\u307e\u3042 \u81ea\u5206\u3067\u4f55\u3068\u304b\u3084\u3063\u3066\u307f\u308b\u3088\u3002\n\u300c\u3075\u3045\u301c\u3093\u3002\u307e\u3042 \u3044\u3044\u3084\u3002\n\u300c\u50d5\u306e\u52a9\u3051\u304c\u5fc5\u8981\u306a\u3089 \u8a00\u3063\u3066\u306d\u3002\n\u30fb\u30fb\u30fb\u30fb\u3002{ct.1.Fr}{ct.2.Fr}{ct.3.Fr}{ct.7.Fr}{ct.8.Fr}{ct.9.Fr}"));}),_XT=new T2(0,_XR,_XS),_XU=new T(function(){return B(unCStr("s0C1"));}),_XV=new T(function(){return B(unCStr("\n\u300c\u3053\u306e\u4e16\u754c\u306b\u306f \u6301\u3066\u308b\u30e2\u30ce\u3002 \u6301\u3066\u306a\u3044\u30e2\u30ce\u3002 \u52d5\u304b\u305b\u308b\u30e2\u30ce\u3002 \u52d5\u304b\u306a\u3044\u30e2\u30ce \u3068\u304b\u304c \u3042\u308b\u3088\u3002\n\u300c\u6301\u3063\u305f\u3082\u306e\u3092 \u81ea\u5206\u306e\u3090\u308b\u6240\u306b\u7f6e\u304f\u5834\u5408\u306f \u30ad\u30fc\u30dc\u30fc\u30c9\u306a\u3089 \u30b9\u30da\u30fc\u30b9\u30ad\u30fc\u3002\n\u300c\u30bf\u30c3\u30c1\u306a\u3089 \u307e\u3093\u306a\u304b\u908a\uff1a\u3078\u3093\uff1a\u3092\u30bf\u30c3\u30d7 \u304b\u306a\u3002"));}),_XW=new T2(0,_XU,_XV),_XX=new T(function(){return B(unCStr("s0C2"));}),_XY=new T(function(){return B(unCStr("\n\u300c\u4e00\u756a\u4e0a\u306e\u884c\u306b =\uff1c\u30a4\u30b3\u30fc\u30eb\uff1e \u304c\u3042\u308b\u3067\u3057\u3087\uff1f\u3002\n\u300c\u30a4\u30b3\u30fc\u30eb \u306f \u305d\u306e\u5de6\u3068 \u53f3\u304c \u7b49\u3057\u3044 \u3063\u3066\u3053\u3068\u3060\u3088\u3002\n\u300c\u30a4\u30b3\u30fc\u30eb \u306e\u5de6\u3068\u53f3\u3092\u7b49\u3057\u304f\u3057\u3066\u3042\u3052\u308c\u3070 \u304d\u3063\u3068\u524d\u306b\u9032\u3081\u308b\u306f\u305a\u3060\u3088\u3002"));}),_XZ=new T2(0,_XX,_XY),_Y0=new T(function(){return B(unCStr("s0C3"));}),_Y1=new T(function(){return B(unCStr("\n\u300c\u4e0a\u306e\u7b49\u5f0f\u3092\u5b8c\u6210\u3055\u305b\u3084\u3046"));}),_Y2=new T2(0,_Y0,_Y1),_Y3=new T(function(){return B(unCStr("s0c"));}),_Y4=new T(function(){return B(unCStr("\n\u300c\u30aa\u30c3\u30b1\u30fc\uff01 \u7c21\uff1a\u304b\u3093\uff1a\u55ae\uff1a\u305f\u3093\uff1a\u3060\u3063\u305f\uff1f\u3002{d.bC}{e.bC.m0:s0C4}\n\u300c\u305d\u308c\u3062\u3083\u3042 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u90e8\uff1a\u3078\uff1a\u5c4b\uff1a\u3084\uff1a\u3078\u3044\u3053\u3063\u304b{p.2,4.n,Ex}{e.un.l}{e.c0.m1:s1}"));}),_Y5=new T2(0,_Y3,_Y4),_Y6=new T(function(){return B(unCStr("s0C4"));}),_Y7=new T(function(){return B(unCStr("\n\u300c\u6b21\u306e\u90e8\u5c4b\u3078 \u3044\u304b\u3046\u3088"));}),_Y8=new T2(0,_Y6,_Y7),_Y9=new T(function(){return B(unCStr("s1"));}),_Ya=new T(function(){return B(unCStr("\n\u3042\u308c\uff1f\u3069\u3053\u884c\u3063\u305f\uff1f\u3002\n\u300c\u307c\u304f\u306e\u3053\u3068\u3092 \u6c23\u306b\u304b\u3051\u3066\u304f\u308c\u308b\u3093\u3060\u3002 \u3042\u308a\u304c\u305f\u3046\uff01\u3002\n\u300c\u3061\u3087\u3063\u3068\u3053\u3053\u306b\u306f \u5c45\uff1a\u3090\uff1a\u306a\u3044\u3051\u3069 \u8a00\u8449\u306f\u805e\u3053\u3078\u3066\u308b\u3067\u3057\u3087\uff1f\u3002\n\u300c\u4f55\u304b\u3042\u3063\u305f\u3089 \u307e\u305f\u7e4b\uff1a\u3064\u306a\uff1a\u304c\u308b\u304b\u3089 \u5927\u4e08\u592b\u3060\u3088\u301c\u3002\n\u3064\u306a\u304c\u308b\uff1f\u3002 \u307e\u3042\u3044\u3044\u3084\u3002\n\u3066\u304b \u3053\u3053\u306f\u4f55\u3060\uff1f{d.bC}{e.b=0.m0:s1Q1}{e.b=1.m0:s1Q2}{e.b=2.m0:s1Q3}{e.bS.m1:s1S0}{e.vC.m1:s1C0}{e.bJ.m1:s1J0:1:s1J1}{e.uR.r}{e.==.m1:s1c}"));}),_Yb=new T2(0,_Y9,_Ya),_Yc=new T(function(){return B(unCStr("s1Q1"));}),_Yd=new T(function(){return B(unCStr("\n\u6e29\u5ba4\u52b9\u679c\u306e\u6bd4\u8f03\u7684\u9ad8\u3044\u30ac\u30b9\u306f\uff1f"));}),_Ye=new T2(0,_Yc,_Yd),_Yf=new T(function(){return B(unCStr("s1Q3"));}),_Yg=new T(function(){return B(unCStr("\n\u4e8c\u9178\u5316\u70ad\u7d20\u306e\u5927\u6c23\u4e2d\u306e\u5272\u5408\u306f\uff1f"));}),_Yh=new T2(0,_Yf,_Yg),_Yi=new T(function(){return B(unCStr("s020"));}),_Yj=new T(function(){return B(unCStr("\n\u300c\u3072\u3068\u3064\u3057\u304b\u306a\u3044\u4e16\u754c\u306e\u4e2d\u306b \u3042\u306a\u305f\u304c\u751f\u304d\u3066\u3090\u308b\u3068\u3044\u3075\u306e\u306f \u5be6\uff1a\u3058\u3064\uff1a\u306f \u3072\u3068\u3064\u306e\u89c0\uff1a\u304b\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u3067\u3042\u308b\u3002\n\u300c\u89c0\u5ff5\u3068\u3044\u3075\u306e\u306f \u3042\u306a\u305f\u306e\u5fc3\u304c\u6c7a\u3081\u3066\u3090\u308b \u4fe1\u3058\u3066\u3090\u308b\u3053\u3068\u304c\u3089\u3067\u3042\u308b\u3002\n\u300c\u305d\u308c\u306f \u3042\u306a\u305f\u306e\u5fc3\u306e\u4e2d\u306b\u3042\u308b \u7b49\uff1a\u3068\u3046\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u3067\u3042\u308b\u3002\n\u300c\u305b\u304b\u3044\u306f \u3072\u3068\u3064 \u305b\u304b\u3044\u306f \u304a\u306a\u3058 \u305b\u304b\u3044\u306f \u307e\u308b\u3044 \u305f\u3060\u3072\u3068\u3064\u3002\n\u300c\u3053\u308c\u306f \u3059\u3079\u3066 \u3042\u306a\u305f\u306e\u5fc3\u306e\u4e2d\u306b\u3042\u308b \u7b49\u5f0f \u3064\u307e\u308a \u89c0\u5ff5\u3067\u3042\u308b\u3002\n\u300c\u305d\u306e\u89c0\u5ff5\u3092 \u6301\u3061\u7e8c\uff1a\u3064\u3065\uff1a\u3051\u308b\u81ea\u7531\u3082 \u305d\u306e\u89c0\u5ff5\u3092 \u5225\u306e\u3082\u306e\u306b\u8b8a\uff1a\u304b\uff1a\u3078\u308b\u81ea\uff1a\u3058\uff1a\u7531\uff1a\u3044\u3046\uff1a\u3082 \u3042\u306a\u305f\u306f\u6301\u3063\u3066\u3090\u308b\u3002"));}),_Yk=new T2(0,_Yi,_Yj),_Yl=new T2(1,_Yk,_10),_Ym=new T(function(){return B(unCStr("s030"));}),_Yn=new T(function(){return B(unCStr("\n\u300c\u73fe\uff1a\u3052\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u306e\u793e\uff1a\u3057\u3083\uff1a\u6703\uff1a\u304b\u3044\uff1a\u3067 \u6700\u3082\u96e3\uff1a\u3080\u3065\u304b\uff1a\u3057\u3044\u3053\u3068\u306f \u3059\u3079\u3066\u304c\u7c21\uff1a\u304b\u3093\uff1a\u55ae\uff1a\u305f\u3093\uff1a\u3067\u3042\u308b\u3053\u3068\u3092 \u7406\uff1a\u308a\uff1a\u89e3\uff1a\u304b\u3044\uff1a\u3059\u308b\u3053\u3068\u3067\u3042\u308b\u3002\n\u300c\u3053\u306e\u4e16\u754c\u306e\u6cd5\uff1a\u306f\u3075\uff1a\u5247\uff1a\u305d\u304f\uff1a \u30eb\u30fc\u30eb\u306f \u975e\uff1a\u3072\uff1a\u5e38\uff1a\u3058\u3083\u3046\uff1a\u306b\u7c21\u55ae\u3067 \u3072\u3068\u3064\u3057\u304b\u306a\u3044\u3002\n\u300c\u305d\u308c\u306f \u8207\uff1a\u3042\u305f\uff1a\u3078\u305f\u3082\u306e\u304c \u8fd4\u3063\u3066\u304f\u308b \u3068\u3044\u3075\u6cd5\u5247 \u305f\u3060\u3072\u3068\u3064\u3067\u3042\u308b\u3002\n\u300c\u3057\u3044\u3066 \u307e\u3046\u3072\u3068\u3064 \u3042\u308b\u3068\u3059\u308c\u3070\u3002\n\u300c\u3042\u306a\u305f\u306f \u5b58\uff1a\u305d\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u3057\u3066\u3090\u308b \u3068\u3044\u3075\u3053\u3068\u3060\u3002"));}),_Yo=new T2(0,_Ym,_Yn),_Yp=new T2(1,_Yo,_Yl),_Yq=new T(function(){return B(unCStr("s080"));}),_Yr=new T(function(){return B(unCStr("\n\u300c\u8089\uff1a\u306b\u304f\uff1a\u9ad4\uff1a\u305f\u3044\uff1a\u304c\u3042\u308b\u304b\u3089\u7cbe\uff1a\u305b\u3044\uff1a\u795e\uff1a\u3057\u3093\uff1a\u304c\u3042\u308b \u3068\u3044\u3075\u306e\u306f \u305d\u308c\u3092\u6b63\u3057\u3044\u3068\u3042\u306a\u305f\u304c\u6c7a\u3081\u305f\u306e\u3067\u3042\u308c\u3070 \u6b63\u3057\u3044\u3002\n\u300c\u7cbe\u795e\u304c\u3042\u308b\u304b\u3089 \u8089\u9ad4\u304c\u3042\u308b \u3068\u3044\u3075\u306e\u306f \u6b63\u3057\u3044\u3002\n\u300c\u305d\u306e\u3053\u3068\u304b\u3089\u306e\u307f \u8089\u9ad4\u304c\u3042\u308b\u304b\u3089\u7cbe\u795e\u304c\u3042\u308b \u3068\u3044\u3075\u8003\u3078\u3092\u80af\uff1a\u3053\u3046\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3059\u308b\u3053\u3068\u304c\u3067\u304d\u308b\u3002\n\u300c\u306a\u305c\u306a\u3089 \u7cbe\u795e\u3092\u5148 \u3068\u3059\u308b\u306e\u3067\u3042\u308c\u3070 \u3042\u306a\u305f\u306e\u89c0\uff1a\u304b\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u304c \u6b63\u3057\u3055\u306e\u57fa\uff1a\u3082\u3068\uff1a\u3092\u306a\u3057\u3066\u3090\u308b\u304b\u3089\u3067\u3042\u308b\u3002\n\u300c\u7cbe\u795e\u304c\u8089\u9ad4\u306e\u524d\u306b\u3042\u308b \u3068\u3044\u3075\u3053\u3068\u306b\u3088\u3063\u3066\u306e\u307f \u8089\u9ad4\u304c\u524d\u3067\u3042\u3063\u3066\u3082\u3088\u3044\u3057 \u7cbe\u795e\u304c\u524d\u3067\u3042\u3063\u3066\u3082\u3088\u3044 \u3068\u3044\u3075\u81ea\u7531\u304c\u751f\u3058\u308b\u3002\n\u300c\u3069\u3061\u3089\u3067\u3082 \u3042\u306a\u305f\u306e\u597d\u304d\u306a\u3084\u3046\u306b \u9078\u3093\u3067\u3088\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306a\u308b\u3002"));}),_Ys=new T2(0,_Yq,_Yr),_Yt=new T2(1,_Ys,_Yp),_Yu=new T(function(){return B(unCStr("s090"));}),_Yv=new T(function(){return B(unCStr("\n\u300c\u89c0\uff1a\u304b\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u304c\u611f\uff1a\u304b\u3093\uff1a\u60c5\uff1a\u3058\u3084\u3046\uff1a\u3092\u751f\u307f \u611f\u60c5\u304c\u884c\uff1a\u304b\u3046\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3092\u4fc3\uff1a\u3046\u306a\u304c\uff1a\u3059\u3002\n\u300c\u3042\u306a\u305f\u306e\u4e16\u754c\u306f \u3042\u306a\u305f\u306e\u89c0\u5ff5\u306b\u3088\u3063\u3066 \u6587\u5b57\u901a\u308a \u5275\uff1a\u3055\u3046\uff1a\u9020\uff1a\u3056\u3046\uff1a\u3055\u308c\u3066\u3090\u308b\u3002\n\u300c\u305d\u306e\u3053\u3068\u3092\u5fd8\uff1a\u308f\u3059\uff1a\u308c\u308b\u3068\u3044\u3075\u306e\u3082 \u3042\u306a\u305f\u304c\u671b\uff1a\u306e\u305e\uff1a\u307f \u5275\uff1a\u3064\u304f\uff1a\u308a\u51fa\u3057\u305f\u3053\u3068\u3002\n\u300c\u89c0\u5ff5\u306f \u3042\u306a\u305f\u306e\u610f\uff1a\u3044\uff1a\u601d\uff1a\u3057\uff1a\u306b\u3088\u3063\u3066 \u8b8a\uff1a\u304b\uff1a\u3048\u308b\u3053\u3068\u304c\u3067\u304d\u308b\u3002\n\u300c\u89c0\u5ff5\u304c\u4e16\u754c\u3092\u5275\u9020\u3057\u3066\u3090\u308b \u3068\u3044\u3075\u3053\u3068\u306f \u3042\u306a\u305f\u306e\u610f\u601d\u304c \u4e16\u754c\u3092\u5275\u9020\u3067\u304d\u308b \u3068\u3044\u3075\u3053\u3068\u3002\n\u300c\u3042\u306a\u305f\u306e\u5468\uff1a\u3057\u3046\uff1a\u56f2\uff1a\u3090\uff1a\u306e \u3059\u3079\u3066\u306e\u72b6\uff1a\u3058\u3083\u3046\uff1a\u6cc1\uff1a\u304d\u3083\u3046\uff1a\u3092 \u3042\u306a\u305f\u304c \u30b3\u30f3\u30c8\u30ed\u30fc\u30eb\u3067\u304d\u308b \u3068\u3044\u3075\u3053\u3068\u3002\n\u300c\u305d\u308c\u3092\u5be6\uff1a\u3058\u3064\uff1a\u884c\uff1a\u304b\u3046\uff1a\u3059\u308b\u3082 \u3057\u306a\u3044\u3082 \u3059\u3079\u3066 \u3042\u306a\u305f\u3060\u3051\u306e\u610f\u601d\u306b\u59d4\uff1a\u3086\u3060\uff1a\u306d\u3089\u308c\u3066\u3090\u308b\u3002"));}),_Yw=new T2(0,_Yu,_Yv),_Yx=new T2(1,_Yw,_Yt),_Yy=new T(function(){return B(unCStr("nubatama"));}),_Yz=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_YA=new T2(0,_Yy,_Yz),_YB=new T2(1,_YA,_Yx),_YC=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_YD=new T(function(){return B(unCStr("msgW"));}),_YE=new T2(0,_YD,_YC),_YF=new T2(1,_YE,_YB),_YG=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u307e\u305b\u3046"));}),_YH=new T(function(){return B(unCStr("msgR"));}),_YI=new T2(0,_YH,_YG),_YJ=new T2(1,_YI,_YF),_YK=new T(function(){return B(unCStr("s2c"));}),_YL=new T(function(){return B(unCStr("\n\u300c\u3059\u3054\u3044\u306d\uff01 \u30af\u30ea\u30a2\u3060\u3088\uff01\u3002{da}"));}),_YM=new T2(0,_YK,_YL),_YN=new T2(1,_YM,_YJ),_YO=new T(function(){return B(unCStr("s2_3"));}),_YP=new T(function(){return B(unCStr("\n\u300c\u3075\u3064\u3046\u30fb\u30fb\u30fb\u3067\u3059\u304b\u30fc\u3002\n\u306a\u306b\u304b\uff1f\u3002\n\u300c\u3044\u3084 \u3079\u3064\u306b \u305d\u308c\u306f\u305d\u308c\u3067 \u3044\u3044\u3093\u3060\u3051\u3069\u306d\u30fc\u3002\n\u300c\u30fb\u30fb\u30fb\u306a\u3093\u304b\u304b\u3046 \u3075\u3064\u3046 \u3063\u3066 \u307b\u3093\u3068\u306f\u30a4\u30e4\u306a\u3093\u3060\u3051\u3069 \u305d\u308c\u8a00\u3072\u305f\u304f\u306a\u3044\u3068\u304d\u306b\u4f7f\u3075\u3084\u3046\u306a\u30a4\u30e1\u30fc\u30b8\u304c\u30fb\u30fb\u3002\n\u3044\u3084 \u55ae\u7d14\u306b\u8208\u5473\u306a\u3044\u3060\u3051\u3060\u304b\u3089\u3002\n\u5acc\u3072\u3067\u3082\u306a\u3044\u3057 \u597d\u304d\u3067\u3082\u306a\u3044\u3002\n\u300c\u3075\u30fc\u3093 \u305d\u3063\u304b\u30fc\u30fb\u30fb\u30fb\u3002\n\u306a\u3093\u3060\u3088\u3002\n\u300c\u307c\u304f\u3061\u3093 \u304b\u308f\u3044\u3044\u3074\u3087\u3093\uff01\u3002\n\u306f\u3044\uff1f"));}),_YQ=new T2(0,_YO,_YP),_YR=new T2(1,_YQ,_YN),_YS=new T(function(){return B(unCStr("s2_2"));}),_YT=new T(function(){return B(unCStr("\n\u300c\u305d\u3063\u304b\u30fc \u305d\u308a\u3083\u6b98\u5ff5\u3002\n\u300c\u307e\u3042 \u30d2\u30c8\u305d\u308c\u305e\u308c\u597d\u307f\u304c\u9055\u3075\u3057 \u4ed5\u65b9\u306a\u3044\u304b\u30fc\u3002\n\u3042\u304b\u3089\u3055\u307e\u306b\u6b98\u5ff5\u3055\u3046\u3060\u306d\u3002\n\u300c\u307e\u3042 \u5acc\u306f\u308c\u308b\u306e\u306f \u597d\u304d\u3062\u3083\u306a\u3044\u3057\u306d\u30fb\u30fb\u30fb\u3002\n\u3079\u3064\u306b \u304a\u524d\u304c\u7279\u5225\u5acc\u3072\u3063\u3066\u3053\u3068\u3067\u3082\u306a\u3044\u3088\u3002\n\u300c\u3055\u3046\u306a\u306e\uff01 \u3084\u3063\u305f\u30fc\uff01\u3002\n\u306a\u3093\u304b\u958b\u304d\u306a\u307b\u308b\u306e\u65e9\u3044\u306a\u30fb\u30fb\u30fb"));}),_YU=new T2(0,_YS,_YT),_YV=new T2(1,_YU,_YR),_YW=new T(function(){return B(unCStr("s2_1"));}),_YX=new T(function(){return B(unCStr("\n\u300c\u3055\u3046\u306a\u3093\u3060\uff01\u3002\n\u300c\u3046\u308c\u3057\u3044\u306a\u3002\n\u3044\u3084 \u3079\u3064\u306b\u4e00\u822c\u7684\u306b \u3068\u3044\u3075\u3060\u3051\u3067 \u7279\u5225\u304a\u524d\u306e\u3053\u3068\u304c \u3063\u3066\u308f\u3051\u3067\u3082\u306a\u3044\u3093\u3060\u30b1\u30c9\u3002\n\u300c\u305d\u308c\u3067\u3082\u3046\u308c\u3057\u3044\u3088\u3002\n\u300c\u30cd\u30b3\u306f\u306d \u901a\u5e38\u4eba\u9593\u304c\u611f\u3058\u3066\u3090\u306a\u3044\u4e16\u754c\u3092\u898b\u3066\u3090\u308b\u3093\u3060\u3002\n\u305d\u308a\u3083 \u4eba\u9593\u3068\u9055\u3075\u52d5\u7269\u306a\u3093\u3060\u304b\u3089 \u3055\u3046\u3044\u3075\u3082\u3093\u3060\u308d\uff1f\u3002\n\u300c\u307e\u3042 \u3055\u3046\u3060\u3051\u3069 \u305d\u306e\u4e16\u754c\u306f \u3068\u3063\u3066\u3082\u30d2\u30c8\u306b\u3068\u3063\u3066\u5927\u4e8b\u306a\u3093\u3060\u3088\u3002\n\u3075\u30fc\u3093\u3002\n\u300c\u3042 \u306a\u3093\u304b\u5168\u7136\u8208\u5473\u306a\u3044\u8a00\u3072\u65b9\u30fb\u30fb\u30fb\n\u307e\u3042\u306d\u3002\n\u300c\u3075\u3093\uff01 \u3044\u3044\u3088\uff01 \u304d\u3063\u3068\u305d\u306e\u3046\u3061\u6c23\u306b\u306a\u3063\u3066\u4ed5\u65b9\u306a\u304f\u306a\u308b\u3093\u3060\u304b\u3089\u301c\u3002"));}),_YY=new T2(0,_YW,_YX),_YZ=new T2(1,_YY,_YV),_Z0=new T(function(){return B(unCStr("s2B0"));}),_Z1=new T(function(){return B(unCStr("\n\u300c\u304a\u306f\u3084\u3046\u3054\u3056\u3044\u307e\u3059"));}),_Z2=new T2(0,_Z0,_Z1),_Z3=new T2(1,_Z2,_YZ),_Z4=new T(function(){return B(unCStr("s2J0"));}),_Z5=new T(function(){return B(unCStr("\n\u300c\u3053\u3093\u306b\u3061\u306f\uff01"));}),_Z6=new T2(0,_Z4,_Z5),_Z7=new T2(1,_Z6,_Z3),_Z8=new T(function(){return B(unCStr("s2Not"));}),_Z9=new T(function(){return B(unCStr("\nNOT"));}),_Za=new T2(0,_Z8,_Z9),_Zb=new T2(1,_Za,_Z7),_Zc=new T(function(){return B(unCStr("s2N"));}),_Zd=new T(function(){return B(unCStr("\n\u5fc5\u9808\u306a\u3053\u3068\u3060"));}),_Ze=new T2(0,_Zc,_Zd),_Zf=new T2(1,_Ze,_Zb),_Zg=new T(function(){return B(unCStr("s2H"));}),_Zh=new T(function(){return B(unCStr("\n\u6709\u5bb3\u3067\u5371\u967a\u3060"));}),_Zi=new T2(0,_Zg,_Zh),_Zj=new T2(1,_Zi,_Zf),_Zk=new T(function(){return B(unCStr("s2I"));}),_Zl=new T(function(){return B(unCStr("\n\u611f\u67d3\u3057\u305f\u3068\u3044\u3075\u3053\u3068"));}),_Zm=new T2(0,_Zk,_Zl),_Zn=new T2(1,_Zm,_Zj),_Zo=new T(function(){return B(unCStr("s2P"));}),_Zp=new T(function(){return B(unCStr("\n\u5b58\u5728\u3057\u3066\u3090\u308b"));}),_Zq=new T2(0,_Zo,_Zp),_Zr=new T2(1,_Zq,_Zn),_Zs=new T(function(){return B(unCStr("s2Q5"));}),_Zt=new T(function(){return B(unCStr("\n\u4eba\u3068\u63a5\u89e6\u3059\u308b\u306e\u306f"));}),_Zu=new T2(0,_Zs,_Zt),_Zv=new T2(1,_Zu,_Zr),_Zw=new T(function(){return B(unCStr("s2Q4"));}),_Zx=new T(function(){return B(unCStr("\n\u30ef\u30af\u30c1\u30f3\u3092\u6253\u3064\u306e\u306f"));}),_Zy=new T2(0,_Zw,_Zx),_Zz=new T2(1,_Zy,_Zv),_ZA=new T(function(){return B(unCStr("s2Q3"));}),_ZB=new T(function(){return B(unCStr("\n\u30de\u30b9\u30af\u3092\u3059\u308b\u306e\u306f"));}),_ZC=new T2(0,_ZA,_ZB),_ZD=new T2(1,_ZC,_Zz),_ZE=new T(function(){return B(unCStr("s2Q2"));}),_ZF=new T(function(){return B(unCStr("\nPCR\u691c\u67fb\u3092\u3057\u3066\u967d\u6027\u306b\u306a\u308b\u3068\u3044\u3075\u3053\u3068\u306f"));}),_ZG=new T2(0,_ZE,_ZF),_ZH=new T2(1,_ZG,_ZD),_ZI=new T(function(){return B(unCStr("s2Q1"));}),_ZJ=new T(function(){return B(unCStr("\n\u65b0\u578b\u30b3\u30ed\u30ca\u30a6\u30a4\u30eb\u30b9\u306f"));}),_ZK=new T2(0,_ZI,_ZJ),_ZL=new T2(1,_ZK,_ZH),_ZM=new T(function(){return B(unCStr("s2"));}),_ZN=new T(function(){return B(unCStr("\n\u300c\u306d\u3048\u306d\u3048 \u7a81\u7136\u3060\u3051\u3069 \u30cd\u30b3\u3063\u3066\u597d\u304d\uff1f{da}{e.b=0.m0:s2Q1}{e.b=1.m0:s2Q2}{e.b=2.m0:s2Q3}{e.b=3.m0:s2Q4}{e.b=4.m0:s2Q5}{e.vP.m1:s2P}{e.vI.m1:s2I}{e.vH.m1:s2H}{e.vN.m1:s2N}{e.bJ.m1:s2J0}{e.bB.m1:s2B0}{e.e/.m1:s2Not}{e.uR.r}{e.==.m1:s2c}{ch.\u597d\u304d,s2_1.\u304d\u3089\u3044,s2_2.\u3075\u3064\u3046,s2_3}"));}),_ZO=new T2(0,_ZM,_ZN),_ZP=new T2(1,_ZO,_ZL),_ZQ=new T(function(){return B(unCStr("s1c"));}),_ZR=new T(function(){return B(unCStr("\n\u300c\u3042\u306a\u305f\u306f \u79c1\u3002\n\u300c\u79c1\u306f \u4e16\u754c\u3002\n\u3048\uff1f \u306a\u306b\uff1f \u3060\u308c\uff1f\u3002\n\u300c\u305d\u308c\u3067\u306f \u6b21\u306b\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046{p.0,3.n,Ex}{e.un.l}{e.c1.m1:s2}"));}),_ZS=new T2(0,_ZQ,_ZR),_ZT=new T2(1,_ZS,_ZP),_ZU=new T(function(){return B(unCStr("s1J1"));}),_ZV=new T(function(){return B(unCStr("\n\u300c\u307e\u305a\u306f \u30ea\u30c7\u30e5\u30fc\u30b9\uff01\u3002\n\u300c\u3053\u308c\u306f \u524a\uff1a\u3055\u304f\uff1a\u6e1b\uff1a\u3052\u3093\uff1a\u3059\u308b \u3068\u3044\u3075\u3053\u3068\u3060\u3002\n\u3062\u3083\u3042 \u306f\u3058\u3081\u304b\u3089 \u3055\u3046\u8a00\u3063\u3066\u3088\u306d\u3002\n\u300c\u4eba\u306e\u8a71\u3092\u906e\u308b\u3082\u306e\u3067\u306f\u306a\u3044\uff01\u3002\u6700\u5f8c\u307e\u3067\u3088\u3046\u3046\u3046\u3046\u304f \u805e\u304d\u306a\u3055\u3044\uff01\u3002\n\u3046\u308f\u3063 \u3081\u3093\u3069\u304f\u3055\u3044\u3084\u3064\u3060\u30fb\u30fb\u30fb\u3002\n\u300c\u3046\u3093\uff1f\n\u3044\u3084 \u306a\u3093\u3067\u3082\u30fb\u30fb\u30fb\n\u300c\u4eba\u985e\u306f \u7279\u306b\u5148\u9032\u56fd\u306b\u304a\u3044\u3066\u306f \u305d\u306e\u5bcc\u306b\u7518\u3093\u3058\u305f\u3053\u3068\u306b\u3088\u308a \u4eba\u3005\u306e\u6d88\u8cbb\u306b\u6b6f\u6b62\u3081\u304c\u52b9\u304b\u306a\u304f\u306a\u3063\u3066\u3044\u308b\u3002\n\u30fb\u30fb\u30fb\u3002\n\u300c\u30fb\u30fb\u30fb\u3002\n\u30fb\u30fb\u30fb\u3002\n\u300c\u304a\u3044\uff01\u3002\n\u3048\uff1f \u4f55\uff1f\u3002\n\u300c\u30ca\u30cb \u3067\u306f\u306a\u3044\uff01 \u3061\u3083\u3093\u3068\u8074\u3044\u3066\u308b\u306e\u304b\uff01\u3002\n\u3044\u3084 \u3042\u3093\u305f\u304c \u8a71\u3092\u906e\u308b\u306a \u3068\u304b\u8a00\u3063\u305f\u304b\u3089\u9ed9\u3063\u3066\u308b\u3060\u3051\u3067\u3057\u3087\u3002\n\u300c\u8074\u3044\u3066\u3090\u308b\u306a\u3089 \u76f8\u69cc\u304f\u3089\u3044\u6253\u3061\u306a\u3055\u3044\uff01\u3002\n\u306f\u3042\u30fb\u30fb\u30fb\u3002\n\u300c\u5927\u91cf\u6d88\u8cbb\u306b\u306f \u5927\u91cf\u306e\u30a8\u30cd\u30eb\u30ae\u30fc\u304c\u5fc5\u8981\u3060\u3002\n\u300c\u305d\u3082\u305d\u3082 \u30a8\u30cd\u30eb\u30ae\u30fc\u306f \u4f55\u3092\u6d88\u8cbb\u3059\u308b\u3053\u3068\u306b\u3088\u308a\u5f97\u3089\u308c\u3066\u3090\u308b\u304b\u77e5\u3063\u3066\u3090\u308b\u304b\uff1f\u3002\n\u3048\uff1f \u98df\u3079\u3082\u306e\uff1f\u3002\n\u300c\u98df\u7269\u306f\u7121\u8ad6\u3060\u304c \u6628\u4eca\u306e\u7d4c\u6e08\u6d3b\u52d5\u306b\u6b20\u304b\u305b\u306a\u3044\u30a8\u30cd\u30eb\u30ae\u30fc\u6e90\u304c\u3042\u308b\u3067\u3042\u3089\u3046\uff1f\u3002\n\u30fb\u30fb\u30fb\u3042\u306e\u30fc \u3082\u3046\u3061\u3087\u3063\u3068\u5206\u304b\u308a\u3084\u3059\u3044\u65e5\u672c\u8a9e\u3067\u3088\u308d\u3057\u304f\u3002\n\u300c\u5168\u304f\u6559\u990a\u306e\u306a\u3044\u4eba\u9593\u306f\u3053\u308c\u3060\u304b\u3089\u56f0\u308b\u3002\n\u300c\u305d\u3082\u305d\u3082\u793c\u5100\u304c\u306a\u3063\u3066\u304a\u3089\u3093\u3002\u305d\u308c\u304c\u4eba\u306b\u3082\u306e\u3092\u805e\u304f\u614b\u5ea6\u304b\uff1f\u3002\n\u3044\u3084 \u3079\u3064\u306b\u4f55\u3082\u5c0b\u306d\u3066\u306a\u3044\u3057\u3002\n\u300c\u304a\u524d\u304c\u7121\u77e5\u3067\u3042\u308b\u3053\u3068\u3092\u6190\u307f \u6559\u3048\u3066\u3084\u3089\u3046\u3068\u3044\u3075\u306e\u3060\u3089\u3046\u3002\n\u3042\u3093\u305f\u3053\u305d\u7121\u793c\u3060\u306a\u3002\n\u300c\u306a\u3093\u3060\u3068\uff01\u3002\n\u306f\u3042 \u307e\u3046\u3044\u3044\u3084 \u3055\u3044\u306a\u3089\u30fc\u3002"));}),_ZW=new T2(0,_ZU,_ZV),_ZX=new T2(1,_ZW,_ZT),_ZY=new T(function(){return B(unCStr("s1J0"));}),_ZZ=new T(function(){return B(unCStr("\n\u300c\u79c1\u306f \u3042\u308b\u653f\u5e9c\u6a5f\u95a2\u6240\u5c5e\u306e \u30b5\u30a4\u30a8\u30f3\u30c6\u30a3\u30b9\u30c8\u3060\u3002\n\u300c\u73fe\u5728 \u5730\u7403\u74b0\u5883\u306f \u5371\u6a5f\u7684\u72b6\u614b\u306b\u7f6e\u304b\u308c\u3066\u3090\u308b\u3002\u6211\u3005\u4eba\u985e\u304c \u5354\u529b\u3057\u3066\u3053\u308c\u306b\u5c0d\u51e6\u3057\u306a\u3051\u308c\u3070 \u5c06\u4f86\u53d6\u308a\u8fd4\u3057\u306e\u3064\u304b\u306a\u3044\u4e8b\u614b\u3092\u62db\u304f\u3053\u3068\u306b\u306a\u308b\u3060\u3089\u3046\u3002\n\u306f\u3042\u30fb\u30fb\u30fb\u3002\n\u300c\u306f\u3042\u30fb\u30fb\u30fb\u3067\u306f\u306a\u3044\u305e\u3002\u771f\u5263\u306b\u8003\u3078\u3066\u307f\u306a\u3055\u3044\u3002\u3042\u306a\u305f\u306e\u884c\u52d5\u306e\u3072\u3068\u3064\u3072\u3068\u3064\u304c \u5730\u7403\u3092\u5b88\u308b\u304b \u6ec5\u307c\u3059\u304b \u6c7a\u3081\u308b\u3068\u8a00\u3063\u3066\u3082\u904e\u8a00\u3067\u306f\u306a\u3044\u306e\u3060\u3002\n\u30fb\u30fb\u30fb\u3063\u3066\u8a00\u306f\u308c\u3066\u3082 \u4f8b\u3078\u3070\u3069\u3093\u306a\u3053\u3068\u3092\u6c23\u3092\u3064\u3051\u308c\u3070\u3044\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c3R\u3060\u3088\u541b\u3002\u30ea\u30c7\u30e5\u30fc\u30b9\u3002\u30ea\u30e6\u30fc\u30ba\u3002\u30ea\u30b5\u30a4\u30af\u30eb\u3002\n\u3042\u30fc \u306a\u3093\u304b\u5b78\u6821\u3067\u304d\u3044\u305f\u3053\u3068\u3042\u308b\u306a\u3002\n\u300c\u805e\u3044\u305f\u3053\u3068\u304c\u3042\u308b\uff1f \u305d\u308c\u3067\u74b0\u5883\u304c\u5b88\u308c\u308b\u3068\u601d\u3075\u306e\u304b\u306d\uff1f \u5be6\u8e10\u3057\u306a\u3051\u308c\u3070\u610f\u5473\u306a\u3044\u306e\u3060\u3088\u3002\n\u30fb\u30fb\u30fb\u3067 \u4f55\u3059\u308c\u3070\u3044\u3044\u3093\u3067\u3057\u305f\u3063\u3051\uff1f\u3002\n\u300c\u306a\u3093\u3068\uff01\u3002 \u3044\u3084\u306f\u3084 \u541b\u306e\u3084\u3046\u306a\u8005\u304c\u5c11\u6578\u6d3e\u3067\u3042\u3063\u3066\u304f\u308c\u308c\u3070\u826f\u3044\u306e\u3060\u304c\u30fb\u30fb\u30fb\u3002\n\u300c\u3088\u308d\u3057\u3044\u3002\u3072\u3068\u3064\u3072\u3068\u3064\u8aac\u660e\u3059\u308b\u304b\u3089 \u3088\u304f\u805e\u304d\u306a\u3055\u3044\u3002\n\u30fb\u30fb\u30fb\u306a\u3093\u304b\u5049\u3055\u3046\u3060\u306a \u3053\u306e\u3072\u3068\u30fb\u30fb\u30fb\u3002\n\u300c\u4f55\u304b\u8a00\u3063\u305f\u304b\uff1f\u3002\n\u3044 \u3044\u3048 \u4f55\u3067\u3082\u306a\u3044\u3067\u3059\u30fb\u30fb\u30fb"));}),_100=new T2(0,_ZY,_ZZ),_101=new T2(1,_100,_ZX),_102=new T(function(){return B(unCStr("s1S1"));}),_103=new T(function(){return B(unCStr("\n\u300c\u6e29\u5ba4\u52b9\u679c\u30ac\u30b9\u3068\u3044\u3075\u8a00\u8449\u3092\u3054\u5b58\u77e5\u3067\u3059\u304b\uff1f\u3002\n\u3048\u3063\u3068 \u3042\u308c\u3060\u3088\u306d \u5730\u7403\u6e29\u6696\u5316\u306e\u539f\u56e0\u306b\u306a\u3063\u3066\u308b\u3063\u3066\u3044\u3075\u30fb\u30fb\u30fb\u30fb\u30fb\u4e8c\u9178\u5316\u70ad\u7d20\uff01\uff01\u3002\n\u300c\u78ba\u304b\u306b\u305d\u308c\u3082 \u3055\u3046\u306a\u306e\u3067\u3059\u304c \u305d\u308c\u3088\u308a\u3082\u3063\u3068 \u6e29\u5ba4\u52b9\u679c\u306e\u9ad8\u3044\u3082\u306e\u304c\u3042\u308a\u307e\u3059\u3002\n\u3048\uff1f\u30fb\u30fb\u30fb\u3046\u30fc\u3093 \u5929\u7136\u30ac\u30b9 \u3068\u304b\uff1f\u3002\n\u300c\u6c34\u84b8\u6c17\u3067\u3059\u3002\n\u6c34\u84b8\u6c23\u30fb\u30fb\u30fb\u6c34\uff01\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059 \u6c34\u3067\u3059\u3002 \u6c34\u306f\u5927\u6c23\u4e2d\u306b\u3042\u3063\u3066 \u6700\u3082\u6e29\u5ba4\u52b9\u679c\u306b\u8ca2\u732e\u3057\u3066\u3090\u307e\u3059\u3002\n\u8ca2\u732e\u30fb\u30fb\u30fb\u3063\u3066\u30fb\u30fb\u30fb\n\u300c\u8ca2\u732e\u3067\u3059\u3002 \u305d\u308c\u304c\u306a\u3051\u308c\u3070 \u5730\u7403\u306f\u4eba\u985e\u306e\u4f4f\u3081\u306a\u3044\u4e0d\u6bdb\u306e\u5730\u3067\u3059\u3002\n\u3067\u3082 \u3042\u308c\u3067\u3057\u3087\uff1f \u6700\u8fd1\u4e8c\u9178\u5316\u70ad\u7d20\u304c\u5897\u3048\u3066 \u6e29\u6696\u5316\u306b\u306a\u3063\u3066\u3090\u308b\u3093\u3067\u3059\u3088\u306d\uff1f\u3002\n\u300c\u306a\u305c \u3055\u3046\u8a00\u3078\u308b\u306e\u3067\u3059\u304b\uff1f\u3002\n\u306a\u305c\u3063\u3066\u30fb\u30fb\u30fb\u79d1\u5b78\u8005\u304c\u3055\u3046\u8a00\u3063\u3066\u308b\u3067\u3057\u3087\uff1f\u3002\n\u300c\u79d1\u5b78\u8005\u304c\u3055\u3046\u8a00\u3063\u3066\u3090\u308b\u304b\u3089 \u3068\u3044\u3075\u7406\u7531\u3067 \u7269\u4e8b\u3092\u8003\u3078\u308b\u306e\u306f \u975e\u79d1\u5b78\u7684\u3067\u3059\u306d\u3002\n\u4e8c\u9178\u5316\u70ad\u7d20\u304c\u6e29\u5ba4\u52b9\u679c\u30ac\u30b9\u3067 \u305d\u308c\u304c\u5897\u3048\u305f\u304b\u3089 \u6e29\u6696\u5316\u304c\u8d77\u3053\u3063\u3066\u3090\u308b\u3093\u3067\u306f\u306a\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c\u5927\u6c23\u4e2d\u306e\u4e8c\u9178\u5316\u70ad\u7d20\u306e\u5272\u5408\u306f \u304a\u3088\u305d400ppm \u3067\u3059\u3002\n\u3048\uff1f\n\u300c0.04\u30d1\u30fc\u30bb\u30f3\u30c8\u3068\u8a00\u3063\u305f\u3089\u5206\u304b\u308a\u3084\u3059\u3044\u3067\u305b\u3046\u304b\uff1f\u3002 \u5c0d\u3057\u3066\u6c34\u84b8\u6c23\u306e\u5272\u5408\u306f \u6e7f\u5ea6\u306b\u3088\u308a\u307e\u3059\u304c \u3060\u3044\u305f\u30445\u30d1\u30fc\u30bb\u30f3\u30c8\u7a0b\u5ea6\u3067\u3059\u3002\n\u6c34\u306e\u65b9\u304c \u5168\u7136\u591a\u3044\u306a\u30fb\u30fb\u30fb\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u4eee\u306b\u4e8c\u9178\u5316\u70ad\u7d20\u306e\u5272\u5408\u304c \u4eca\u306e\u5341\u500d\u306b\u306a\u3063\u305f\u3068\u3057\u3066 \u305d\u306e\u5927\u6c23\u4e2d\u306e\u5272\u5408\u306f 0.4\u30d1\u30fc\u30bb\u30f3\u30c8\u3067\u3059\u3002 \u6c34\u84b8\u6c23\u306b\u306f\u53ca\u3073\u307e\u305b\u3093\u3002\n\u300c\u305d\u3057\u3066 \u6c34\u84b8\u6c23\u306e\u65b9\u304c \u6e29\u5ba4\u52b9\u679c\u304c\u9ad8\u3044\u306e\u3067\u3059\u3002 \u79c1\u306e\u8a00\u306f\u3046\u3068\u3057\u3066\u3090\u308b\u3053\u3068\u304c\u5206\u304b\u308a\u307e\u3059\u304b\uff1f\u3002\n\u30fb\u30fb\u30fb\u4e8c\u9178\u5316\u70ad\u7d20\u304c\u6e29\u6696\u5316\u306e\u539f\u56e0\u30fb\u30fb\u30fb\u3067\u306f\u306a\u3044\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u79d1\u5b78\u7684\u306a\u30c7\u30fc\u30bf\u304b\u3089 \u5408\u7406\u7684\u306b\u8003\u3078\u308c\u3070 \u4e8c\u9178\u5316\u70ad\u7d20\u304c\u5897\u3048\u3066\u3082 \u5730\u7403\u306e\u6c17\u6e29\u306b\u307b\u3068\u3093\u3069\u5f71\u97ff\u3092\u8207\u3078\u306a\u3044\u3067\u3042\u308d\u3046\u3053\u3068\u304f\u3089\u3044 \u5c0f\u5b78\u751f\u3067\u3082\u5206\u304b\u308a\u307e\u3059\u3002 \u3067\u3059\u304c \u6b98\u5ff5\u306a\u304c\u3089 \u305d\u306e\u5c0f\u5b78\u751f\u9054\u304c\u901a\u3075\u5b78\u6821\u306b\u304a\u3044\u3066 \u975e\u79d1\u5b78\u7684\u306a\u8ff7\u4fe1\u304c\u5e38\u306b\u6559\u3078\u3089\u308c\u3066\u3090\u308b\u306e\u3067\u3059\u3002\n\u3069\u3046\u3057\u3066\u30fb\u30fb\u30fb\uff1f\u3002\n\u300c\u3055\u3066 \u3069\u3046\u3057\u3066\u3067\u305b\u3046\uff1f\u3002"));}),_104=new T2(0,_102,_103),_105=new T2(1,_104,_101),_106=new T(function(){return B(unCStr("s1S0"));}),_107=new T(function(){return B(unCStr("\n\u300c\u79c1\u306f \u79d1\u5b78\u8005\u306e\u7aef\u304f\u308c\u3068\u3057\u3066 \u73fe\u5728\u306e\u74b0\u5883\u554f\u984c\u306e\u6349\u3078\u65b9\u306b\u5c0d\u3057 \u5927\u3044\u306b \u5371\u60e7\u3057\u3066\u3090\u307e\u3059\u3002\n\uff1f\uff1f\uff1f \u3042\u306e\u301c \u307e\u3046\u5c11\u3057\u5206\u304b\u308a\u3084\u3059\u304f \u8a71\u3057\u3066\u3082\u3089\u3078\u307e\u3059\uff1f\u3002\n\u300c\u3042\u3042 \u3059\u307f\u307e\u305b\u3093\u30fb\u30fb\u30fb\u3002 \u79c1\u306f \u305f\u3060 \u3044\u306f\u3086\u308b \u74b0\u5883\u554f\u984c\u3068\u3044\u3075\u3082\u306e\u304c \u554f\u984c\u3067\u3042\u308b \u3068\u8a34\u3078\u305f\u3044\u3060\u3051\u306a\u306e\u3067\u3059\u3002\n\u74b0\u5883\u554f\u984c\u304c\u30fb\u30fb\u30fb\u554f\u984c\uff1f \u3067\u3059\u304b\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u3048\u301c\u3068\u3067\u3059\u306d\u3002 \u8981\u306f \u5730\u7403\u74b0\u5883\u306b\u554f\u984c\u304c\u3042\u308b\u306e\u3067\u306f\u306a\u304f \u73fe\u5728\u306e\u5730\u7403\u74b0\u5883\u306e\u6271\u3072\u65b9 \u3068\u3089\u3078\u65b9\u306b\u554f\u984c\u304c\u3042\u308b \u3068\u8a00\u3063\u3066\u3090\u308b\u306e\u3067\u3059\u3002\n\u306f\u3042\u30fb\u30fb\u30fb\u3002\n\u300c\u4f8b\u3078\u3070 \u5730\u7403\u6e29\u6696\u5316\u554f\u984c \u3068\u3044\u3075\u3082\u306e\u304c\u3042\u308a\u307e\u3059\u3002\n\u3042\u3042 \u5730\u7403\u6e29\u6696\u5316\u306d\uff01 \u305d\u308c\u306a\u3089 \u77e5\u3063\u3066\u307e\u3059\u3088\u3002 \u30c6\u30ec\u30d3\u3067\u3082 \u3088\u304f\u3084\u3063\u3066\u3090\u307e\u3059\u3088\u306d\u3002\n\u300c\u306f\u3044\u3002 \u79c1\u9054\u306e\u898b\u5730\u304b\u3089 \u305d\u308c\u306b\u3064\u3044\u3066\u306e\u756a\u7d44\u306a\u3069\u3092\u898b\u308b\u3068 \u79d1\u5b78\u7684\u306b\u898b\u3066 \u305d\u308c\u3089\u306f \u4e0d\u6b63\u78ba\u306a\u60c5\u5831\u3067\u3059\u3002\n\u30fb\u30fb\u30fb\u3048\u3063\u3068\u30fb\u30fb\u30fb\u3069\u3046\u3044\u3075\u3053\u3068\u304b\u306a\uff1f\u3002\n\u300c\u30c6\u30ec\u30d3\u3067\u8a00\u3063\u3066\u3090\u308b\u3053\u3068\u306f \u9593\u9055\u3063\u3066\u3090\u308b \u3068\u8a00\u3072\u305f\u3044\u306e\u3067\u3059\u3002\n\u3048\uff1f \u3044\u3084 \u3067\u3082 \u5b78\u6821\u3067\u3082\u7fd2\u3075\u3060\u3089\u3046\u3057 \u4f55\u3088\u308a\u3082 \u653f\u5e9c\u304c \u74b0\u5883\u554f\u984c\u306b\u53d6\u308a\u7d44\u3093\u3067\u3090\u308b\u3093\u3062\u3083\u306a\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c\u3055\u3046\u3067\u3059\u3002 \u305d\u3053\u304c\u3084\u3063\u304b\u3044\u306a\u3068\u3053\u308d\u306a\u306e\u3067\u3059\u3002 \u9593\u9055\u3063\u305f\u4e8b\u3092 \u5b78\u6821\u3067\u6559\u3078 \u570b\u3084\u81ea\u6cbb\u9ad4\u304c\u653f\u7b56\u3068\u3057\u3066\u5be6\u884c\u3057\u3066\u3090\u308b\u30fb\u30fb\u30fb\u3002\n\u3044\u3084\u3044\u3084 \u305d\u308c\u306f\u306a\u3044\u3067\u305b\u3046\u3002 \u3060\u3063\u3066 \u79d1\u5b78\u8005\u306e\u4eba\u305f\u3061\u304c\u96c6\u307e\u3063\u3066\u6c7a\u3081\u305f\u3084\u3046\u306a\u3053\u3068\u3092 \u6559\u3078\u305f\u308a \u653f\u6cbb\u5bb6\u304c\u3084\u3063\u305f\u308a\u3059\u308b\u3093\u3062\u3083\u306a\u3044\u3093\u3067\u3059\u304b\uff1f\u3002\n\u300c\u3082\u3061\u308d\u3093 \u3055\u3046\u3042\u3063\u3066\u6b32\u3057\u3044\u3093\u3067\u3059\u304c \u79c1\u3069\u3082\u304b\u3089\u898b\u3066 \u3055\u3046\u3044\u3063\u305f \u3044\u306f\u3086\u308b \uff1c\u79d1\u5b78\u8005\uff1e\u306f \u79d1\u5b78\u3092\u3084\u3063\u3066\u3090\u307e\u305b\u3093\u3002\n\uff1f\uff1f\uff1f \u3069\u3046\u3044\u3075\u3053\u3068\u304b\u306a\uff1f{e.bS.m1:s1S1}"));}),_108=new T2(0,_106,_107),_109=new T2(1,_108,_105),_10a=new T(function(){return B(unCStr("s1C0"));}),_10b=new T(function(){return B(unCStr("\n\u3042\u308c \u3053\u308c\u306f\u30cd\u30b3\uff1f \u3062\u3083\u306a\u3044\u306e\u304b\uff1f\u3002\n\u300c\u50d5\u306f\u3053\u3053\u3060\u3088\u3002\n\u3093\uff1f\n\u300c\u3061\u3087\u3063\u3068\u6b21\u5143\u304c\u9055\u3075\u6240\u30fb\u30fb\u30fb\u3002\u307e\u3042 \u305d\u308c\u306f\u3044\u3044\u3068\u3057\u3066\u3002\n\u300c\u305d\u308c\u306f \u6587\u5b57 C \u3060\u306d\u3002\n\u300c\u305d\u308c\u3092\u52d5\u304b\u3057\u3066 \u3069\u3053\u304b\u3078\u7f6e\u304b\u306a\u304d\u3083\u3044\u3051\u306a\u3044\u304b\u3082\u77e5\u308c\u306a\u3044\u3057 \u7f6e\u304b\u306a\u304f\u3066\u3044\u3044\u304b\u3082\u3057\u308c\u306a\u3044\u3002\n\uff1f\uff1f\uff1f\u306a\u3093\u3060\u305d\u308c\u3002\n\u300c\u3053\u3053\u306b\u306f \u554f\u984c\u304c3\u3064\u3042\u308b\u307f\u305f\u3044\u306a\u3093\u3060\u3002\u305d\u306e\u7b54\u3078\u306b\u306a\u308b\u3082\u306e\u3092 \u30a4\u30b3\u30fc\u30eb\u306e\u53f3\u306b\u7f6e\u304f\u3093\u3060\u3089\u3046\u306d\u3002\n\u300c\u898b\u305f\u3068\u3053\u308d \u6578\u5b57\u3084\u5c0f\u6578\u9ede\uff1f\u306f\u6301\u3066\u308b\u3051\u3069 C \u3068 O \u3068 H \u3068 X \u306f\u6301\u3066\u306a\u304f\u3066 \u52d5\u304b\u3059\u307f\u305f\u3044\u3060\u306d\u3002\n\u30fb\u30fb\u30fb\u30fb\u3002\n\u300c\u3042\u3068 \u3053\u3053\u306b\u306f \u4e8c\u4eba\u306e \u81ea\u79f0 \u79d1\u5b78\u8005\u304c\u3090\u308b\u3088\u3002\u5f7c\u3089\u3068\u8a71\u305b\u3070 \u554f\u984c\u3092\u89e3\u304f\u30d2\u30f3\u30c8\u304c\u5f97\u3089\u308c\u3055\u3046\u3060\u306d\u3002\n\u3066\u304b \u306a\u3093\u3067\u3053\u3093\u306a\u3053\u3068\u3057\u306a\u304d\u3083\u30fb\u30fb\u30fb\u3002\n\u300c\u3062\u3083 \u304c\u3093\u3070\u3063\u3066\u306d\u301c\u3002\u3042 \u3055\u3046\u3060\u3002\u8a00\u3072\u5fd8\u308c\u3066\u305f\u3002\n\u30fb\u30fb\u30fb\u306a\u3093\u3060\u3088\u3002\n\u300c\u3082\u3057\u884c\u304d\u8a70\u307e\u3063\u305f\u3089 \u53f3\u4e0b\u306b\u3042\u308b R \u3078\u98db\u3073\u3053\u3080\u3068\u3044\u3044\u3088\u3002\u305d\u308c\u3062\u3083\uff01\u3002\n\u98db\u3073\u3053\u3080\uff1f\uff1f\uff1f\u3002\u306a\u3093\u304b \u8272\u3005\u8aac\u660e\u4e0d\u8db3\u3060\u308d\u30fb\u30fb\u30fb"));}),_10c=new T2(0,_10a,_10b),_10d=new T2(1,_10c,_109),_10e=new T2(1,_Yh,_10d),_10f=new T(function(){return B(unCStr("s1Q2"));}),_10g=new T(function(){return B(unCStr("\n\u5730\u7403\u306e\u6c17\u6e29\u306f\u6642\u4ee3\u306b\u3088\u3063\u3066\u5927\u304d\u304f\u8b8a\u5316\u3057\u3066\u304d\u305f\uff1f"));}),_10h=new T2(0,_10f,_10g),_10i=new T2(1,_10h,_10e),_10j=new T2(1,_Ye,_10i),_10k=new T2(1,_Yb,_10j),_10l=new T2(1,_Y8,_10k),_10m=new T2(1,_Y5,_10l),_10n=new T2(1,_Y2,_10m),_10o=new T2(1,_XZ,_10n),_10p=new T2(1,_XW,_10o),_10q=new T2(1,_XT,_10p),_10r=new T(function(){return B(unCStr("initMsg"));}),_10s=new T(function(){var _10t=B(_XK(_10r,_XQ,_10q));return new T2(0,_10t.a,_10t.b);}),_10u=new T(function(){return E(E(_10s).b);}),_10v=new T(function(){return E(E(_10s).a);}),_10w=function(_10x){if(!B(_4B(_fp,_10x,_10v))){return __Z;}else{return new F(function(){return _77(_10u,B(_jf(_fp,_10x,_10v)));});}},_10y=10,_10z=15,_10A=new T2(0,_10z,_10y),_10B=new T2(1,_10A,_10),_10C=8,_10D=7,_10E=new T2(0,_10D,_10C),_10F=new T2(1,_10E,_10B),_10G=5,_10H=new T2(0,_10G,_10G),_10I=new T2(1,_10H,_10F),_10J=4,_10K=new T2(0,_10J,_10G),_10L=new T2(1,_10K,_10),_10M=3,_10N=new T2(0,_10M,_10M),_10O=new T2(1,_10N,_10L),_10P=2,_10Q=1,_10R=new T2(0,_10P,_10Q),_10S=new T2(1,_10R,_10O),_10T=new T(function(){return B(_a2("Check.hs:(80,7)-(85,39)|function chAnd"));}),_10U=38,_10V=new T(function(){return B(unCStr("@@@"));}),_10W=new T2(0,_10P,_10M),_10X=1,_10Y=67,_10Z=new T2(0,_10Y,_10X),_110=new T2(0,_10W,_10Z),_111=new T2(0,_10J,_10J),_112=57,_113=new T2(0,_112,_10X),_114=new T2(0,_111,_113),_115=new T2(1,_114,_10),_116=0,_117=new T2(0,_116,_10J),_118=51,_119=new T2(0,_118,_10X),_11a=new T2(0,_117,_119),_11b=new T2(1,_11a,_115),_11c=new T2(0,_10J,_10M),_11d=56,_11e=new T2(0,_11d,_10X),_11f=new T2(0,_11c,_11e),_11g=new T2(1,_11f,_11b),_11h=new T2(1,_110,_11g),_11i=new T2(0,_116,_10M),_11j=50,_11k=new T2(0,_11j,_10X),_11l=new T2(0,_11i,_11k),_11m=new T2(1,_11l,_11h),_11n=new T2(0,_10J,_10P),_11o=55,_11p=new T2(0,_11o,_10X),_11q=new T2(0,_11n,_11p),_11r=new T2(1,_11q,_11m),_11s=new T2(0,_116,_10P),_11t=49,_11u=new T2(0,_11t,_10X),_11v=new T2(0,_11s,_11u),_11w=new T2(1,_11v,_11r),_11x=new T2(0,_10M,_116),_11y=43,_11z=new T2(0,_11y,_10X),_11A=new T2(0,_11x,_11z),_11B=new T2(1,_11A,_11w),_11C=new T2(0,_10Q,_116),_11D=61,_11E=new T2(0,_11D,_10X),_11F=new T2(0,_11C,_11E),_11G=new T2(1,_11F,_11B),_11H=new T2(0,_116,_116),_11I=53,_11J=new T2(0,_11I,_10X),_11K=new T2(0,_11H,_11J),_11L=new T2(1,_11K,_11G),_11M=6,_11N=new T2(0,_11M,_10D),_11O=2,_11P=82,_11Q=new T2(0,_11P,_11O),_11R=new T2(0,_11N,_11Q),_11S=new T2(1,_11R,_10),_11T=48,_11U=new T2(0,_11T,_CD),_11V=new T2(0,_10J,_10D),_11W=new T2(0,_11V,_11U),_11X=new T2(1,_11W,_11S),_11Y=new T2(0,_10P,_10D),_11Z=new T2(0,_11Y,_11U),_120=new T2(1,_11Z,_11X),_121=52,_122=new T2(0,_121,_CD),_123=new T2(0,_116,_10D),_124=new T2(0,_123,_122),_125=new T2(1,_124,_120),_126=3,_127=79,_128=new T2(0,_127,_126),_129=new T2(0,_10G,_11M),_12a=new T2(0,_129,_128),_12b=new T2(1,_12a,_125),_12c=46,_12d=new T2(0,_12c,_CD),_12e=new T2(0,_10M,_11M),_12f=new T2(0,_12e,_12d),_12g=new T2(1,_12f,_12b),_12h=new T2(0,_10Q,_11M),_12i=new T2(0,_12h,_128),_12j=new T2(1,_12i,_12g),_12k=new T2(0,_11j,_CD),_12l=new T2(0,_11M,_10G),_12m=new T2(0,_12l,_12k),_12n=new T2(1,_12m,_12j),_12o=new T2(0,_10M,_10G),_12p=72,_12q=new T2(0,_12p,_126),_12r=new T2(0,_12o,_12q),_12s=new T2(1,_12r,_12n),_12t=new T2(0,_116,_10G),_12u=new T2(0,_12t,_12k),_12v=new T2(1,_12u,_12s),_12w=74,_12x=new T2(0,_12w,_10X),_12y=new T2(0,_10G,_10J),_12z=new T2(0,_12y,_12x),_12A=new T2(1,_12z,_12v),_12B=new T2(0,_10M,_10J),_12C=88,_12D=new T2(0,_12C,_126),_12E=new T2(0,_12B,_12D),_12F=new T2(1,_12E,_12A),_12G=new T2(0,_10Q,_10J),_12H=83,_12I=new T2(0,_12H,_10X),_12J=new T2(0,_12G,_12I),_12K=new T2(1,_12J,_12F),_12L=new T2(0,_10G,_10M),_12M=new T2(0,_10Y,_126),_12N=new T2(0,_12L,_12M),_12O=new T2(1,_12N,_12K),_12P=54,_12Q=new T2(0,_12P,_CD),_12R=new T2(0,_11i,_12Q),_12S=new T2(1,_12R,_12O),_12T=new T2(0,_10P,_10P),_12U=new T2(0,_12T,_11E),_12V=new T2(1,_12U,_12S),_12W=new T2(0,_10Q,_10P),_12X=new T2(0,_12W,_119),_12Y=new T2(1,_12X,_12V),_12Z=81,_130=new T2(0,_12Z,_10X),_131=new T2(0,_11s,_130),_132=new T2(1,_131,_12Y),_133=new T2(0,_10R,_11E),_134=new T2(1,_133,_132),_135=new T2(0,_10Q,_10Q),_136=new T2(0,_135,_11k),_137=new T2(1,_136,_134),_138=new T2(0,_116,_10Q),_139=new T2(0,_138,_130),_13a=new T2(1,_139,_137),_13b=new T2(0,_10P,_116),_13c=new T2(0,_13b,_11E),_13d=new T2(1,_13c,_13a),_13e=new T2(0,_11C,_11u),_13f=new T2(1,_13e,_13d),_13g=new T2(0,_11H,_130),_13h=new T2(1,_13g,_13f),_13i=new T2(0,_11H,_10Z),_13j=new T2(0,_127,_10X),_13k=new T2(0,_11C,_13j),_13l=86,_13m=new T2(0,_13l,_10X),_13n=new T2(0,_13b,_13m),_13o=73,_13p=new T2(0,_13o,_10X),_13q=new T2(0,_11x,_13p),_13r=68,_13s=new T2(0,_13r,_10X),_13t=new T2(0,_10J,_116),_13u=new T2(0,_13t,_13s),_13v=new T2(0,_10G,_116),_13w=new T2(0,_13v,_11u),_13x=new T2(0,_11M,_116),_13y=new T2(0,_13x,_113),_13z=new T2(0,_10D,_10Q),_13A=new T2(0,_13z,_13p),_13B=new T2(0,_10C,_10Q),_13C=84,_13D=new T2(0,_13C,_10X),_13E=new T2(0,_13B,_13D),_13F=9,_13G=new T2(0,_13F,_10Q),_13H=new T2(0,_13G,_13p),_13I=new T2(0,_10y,_10Q),_13J=new T2(0,_13I,_13m),_13K=69,_13L=new T2(0,_13K,_10X),_13M=11,_13N=new T2(0,_13M,_10Q),_13O=new T2(0,_13N,_13L),_13P=12,_13Q=new T2(0,_13P,_10Q),_13R=new T2(0,_13Q,_11E),_13S=77,_13T=new T2(0,_13S,_10X),_13U=new T2(0,_11s,_13T),_13V=65,_13W=new T2(0,_13V,_10X),_13X=new T2(0,_12W,_13W),_13Y=new T2(0,_12T,_12I),_13Z=75,_140=new T2(0,_13Z,_10X),_141=new T2(0,_10M,_10P),_142=new T2(0,_141,_140),_143=new T2(0,_11n,_11E),_144=new T2(0,_11i,_13m),_145=new T2(0,_10Q,_10M),_146=new T2(0,_145,_13W),_147=new T2(0,_10N,_10Z),_148=new T2(0,_11c,_13p),_149=78,_14a=new T2(0,_149,_10X),_14b=new T2(0,_12L,_14a),_14c=new T2(0,_11M,_10M),_14d=new T2(0,_14c,_13L),_14e=new T2(0,_10D,_10M),_14f=new T2(0,_14e,_11E),_14g=80,_14h=new T2(0,_14g,_126),_14i=new T2(0,_13P,_10M),_14j=new T2(0,_14i,_14h),_14k=new T2(0,_117,_10Z),_14l=new T2(0,_12G,_13j),_14m=new T2(0,_10P,_10J),_14n=new T2(0,_14m,_14a),_14o=new T2(0,_12B,_13D),_14p=new T2(0,_111,_13W),_14q=47,_14r=new T2(0,_14q,_CD),_14s=new T2(0,_13P,_13F),_14t=new T2(0,_14s,_14r),_14u=new T2(1,_14t,_10),_14v=new T2(0,_10C,_13F),_14w=new T2(0,_14v,_14r),_14x=new T2(1,_14w,_14u),_14y=new T2(0,_10Q,_13F),_14z=new T2(0,_14y,_11Q),_14A=new T2(1,_14z,_14x),_14B=new T2(0,_13o,_126),_14C=new T2(0,_13P,_10D),_14D=new T2(0,_14C,_14B),_14E=new T2(1,_14D,_14A),_14F=new T2(0,_10C,_10D),_14G=new T2(0,_14F,_12q),_14H=new T2(1,_14G,_14E),_14I=new T2(0,_11V,_12x),_14J=new T2(1,_14I,_14H),_14K=new T2(0,_149,_126),_14L=new T2(0,_10Q,_10D),_14M=new T2(0,_14L,_14K),_14N=new T2(1,_14M,_14J),_14O=new T2(0,_13P,_10G),_14P=new T2(0,_14O,_12q),_14Q=new T2(1,_14P,_14N),_14R=66,_14S=new T2(0,_14R,_10X),_14T=new T2(0,_10C,_10G),_14U=new T2(0,_14T,_14S),_14V=new T2(1,_14U,_14Q),_14W=new T2(0,_10D,_10J),_14X=new T2(0,_14W,_11E),_14Y=new T2(1,_14X,_14V),_14Z=new T2(0,_11M,_10J),_150=new T2(0,_14Z,_13D),_151=new T2(1,_150,_14Y),_152=new T2(0,_12y,_10Z),_153=new T2(1,_152,_151),_154=new T2(1,_14p,_153),_155=new T2(1,_14o,_154),_156=new T2(1,_14n,_155),_157=new T2(1,_14l,_156),_158=new T2(1,_14k,_157),_159=new T2(1,_14j,_158),_15a=new T2(1,_14f,_159),_15b=new T2(1,_14d,_15a),_15c=new T2(1,_14b,_15b),_15d=new T2(1,_148,_15c),_15e=new T2(1,_147,_15d),_15f=new T2(1,_110,_15e),_15g=new T2(1,_146,_15f),_15h=new T2(1,_144,_15g),_15i=new T2(1,_143,_15h),_15j=new T2(1,_142,_15i),_15k=new T2(1,_13Y,_15j),_15l=new T2(1,_13X,_15k),_15m=new T2(1,_13U,_15l),_15n=new T2(1,_13R,_15m),_15o=new T2(1,_13O,_15n),_15p=new T2(1,_13J,_15o),_15q=new T2(1,_13H,_15p),_15r=new T2(1,_13E,_15q),_15s=new T2(1,_13A,_15r),_15t=new T2(0,_11M,_10Q),_15u=new T2(0,_15t,_12I),_15v=new T2(1,_15u,_15s),_15w=new T2(0,_10G,_10Q),_15x=new T2(0,_15w,_13j),_15y=new T2(1,_15x,_15v),_15z=new T2(0,_14g,_10X),_15A=new T2(0,_10J,_10Q),_15B=new T2(0,_15A,_15z),_15C=new T2(1,_15B,_15y),_15D=new T2(0,_11P,_10X),_15E=new T2(0,_10R,_15D),_15F=new T2(1,_15E,_15C),_15G=new T2(0,_135,_10Z),_15H=new T2(1,_15G,_15F),_15I=new T2(0,_138,_15z),_15J=new T2(1,_15I,_15H),_15K=new T2(0,_10D,_116),_15L=new T2(0,_15K,_11E),_15M=new T2(1,_15L,_15J),_15N=new T2(1,_13y,_15M),_15O=new T2(1,_13w,_15N),_15P=new T2(1,_13u,_15O),_15Q=new T2(1,_13q,_15P),_15R=new T2(1,_13n,_15Q),_15S=new T2(1,_13k,_15R),_15T=new T2(1,_13i,_15S),_15U=new T2(1,_15T,_10),_15V=new T2(1,_13h,_15U),_15W=new T2(1,_11L,_15V),_15X=6,_15Y=7,_15Z=8,_160=4,_161=5,_162=function(_163){var _164=E(_163);if(!_164._){return __Z;}else{var _165=_164.b,_166=E(_164.a),_167=_166.b,_168=E(_166.a),_169=function(_16a){if(E(_168)==32){return new T2(1,_166,new T(function(){return B(_162(_165));}));}else{switch(E(_167)){case 0:return new T2(1,new T2(0,_168,_CD),new T(function(){return B(_162(_165));}));case 1:return new T2(1,new T2(0,_168,_15Y),new T(function(){return B(_162(_165));}));case 2:return new T2(1,new T2(0,_168,_11O),new T(function(){return B(_162(_165));}));case 3:return new T2(1,new T2(0,_168,_126),new T(function(){return B(_162(_165));}));case 4:return new T2(1,new T2(0,_168,_160),new T(function(){return B(_162(_165));}));case 5:return new T2(1,new T2(0,_168,_161),new T(function(){return B(_162(_165));}));case 6:return new T2(1,new T2(0,_168,_15X),new T(function(){return B(_162(_165));}));case 7:return new T2(1,new T2(0,_168,_15Y),new T(function(){return B(_162(_165));}));default:return new T2(1,new T2(0,_168,_15Z),new T(function(){return B(_162(_165));}));}}};if(E(_168)==32){return new F(function(){return _169(_);});}else{switch(E(_167)){case 0:return new T2(1,new T2(0,_168,_15Z),new T(function(){return B(_162(_165));}));case 1:return new F(function(){return _169(_);});break;case 2:return new F(function(){return _169(_);});break;case 3:return new F(function(){return _169(_);});break;case 4:return new F(function(){return _169(_);});break;case 5:return new F(function(){return _169(_);});break;case 6:return new F(function(){return _169(_);});break;case 7:return new F(function(){return _169(_);});break;default:return new F(function(){return _169(_);});}}}},_16b=function(_16c){var _16d=E(_16c);return (_16d._==0)?__Z:new T2(1,new T(function(){return B(_162(_16d.a));}),new T(function(){return B(_16b(_16d.b));}));},_16e=function(_16f){var _16g=E(_16f);if(!_16g._){return __Z;}else{var _16h=_16g.b,_16i=E(_16g.a),_16j=_16i.b,_16k=E(_16i.a),_16l=function(_16m){if(E(_16k)==32){return new T2(1,_16i,new T(function(){return B(_16e(_16h));}));}else{switch(E(_16j)){case 0:return new T2(1,new T2(0,_16k,_CD),new T(function(){return B(_16e(_16h));}));case 1:return new T2(1,new T2(0,_16k,_10X),new T(function(){return B(_16e(_16h));}));case 2:return new T2(1,new T2(0,_16k,_11O),new T(function(){return B(_16e(_16h));}));case 3:return new T2(1,new T2(0,_16k,_126),new T(function(){return B(_16e(_16h));}));case 4:return new T2(1,new T2(0,_16k,_160),new T(function(){return B(_16e(_16h));}));case 5:return new T2(1,new T2(0,_16k,_161),new T(function(){return B(_16e(_16h));}));case 6:return new T2(1,new T2(0,_16k,_15X),new T(function(){return B(_16e(_16h));}));case 7:return new T2(1,new T2(0,_16k,_10X),new T(function(){return B(_16e(_16h));}));default:return new T2(1,new T2(0,_16k,_15Z),new T(function(){return B(_16e(_16h));}));}}};if(E(_16k)==32){return new F(function(){return _16l(_);});}else{if(E(_16j)==8){return new T2(1,new T2(0,_16k,_CD),new T(function(){return B(_16e(_16h));}));}else{return new F(function(){return _16l(_);});}}}},_16n=function(_16o){var _16p=E(_16o);return (_16p._==0)?__Z:new T2(1,new T(function(){return B(_16e(_16p.a));}),new T(function(){return B(_16n(_16p.b));}));},_16q=new T(function(){return B(unCStr("msgW"));}),_16r=new T(function(){return B(_10w(_16q));}),_16s=new T(function(){return B(_lu("Check.hs:131:22-33|(ch : po)"));}),_16t=new T(function(){return B(_a2("Check.hs:(101,1)-(144,25)|function trEvent"));}),_16u=new T(function(){var _16v=E(_10V);if(!_16v._){return E(_dJ);}else{return E(_16v.a);}}),_16w=new T(function(){return B(_Xh(_10G,5,_11L));}),_16x=function(_16y){var _16z=E(_16y);return E(_VS);},_16A=new T(function(){return B(unCStr("msgR"));}),_16B=new T(function(){return B(_10w(_16A));}),_16C=function(_16D,_16E,_16F,_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_16Q,_16R,_16S,_16T,_16U,_16V,_16W,_16X,_16Y,_16Z,_170,_171,_172,_173,_174,_175,_176,_177,_178){var _179=E(_16E);if(!_179._){return E(_16t);}else{var _17a=_179.b,_17b=E(_179.a);switch(E(_17b)){case 97:var _17c=new T(function(){var _17d=E(_17a);if(!_17d._){return E(_16s);}else{return new T2(0,_17d.a,_17d.b);}}),_17e=new T(function(){var _17f=B(_Sn(E(_17c).b));return new T2(0,_17f.a,_17f.b);}),_17g=B(_Az(B(_o8(_VQ,new T(function(){return E(E(_17e).b);})))));if(!_17g._){return E(_VX);}else{if(!E(_17g.b)._){var _17h=new T(function(){var _17i=B(_Az(B(_o8(_VQ,new T(function(){return E(E(_17e).a);})))));if(!_17i._){return E(_VX);}else{if(!E(_17i.b)._){return E(_17i.a);}else{return E(_VW);}}},1);return {_:0,a:E(_16F),b:E(_16G),c:E(B(_ny(_17h,E(_17g.a),new T(function(){return E(E(_17c).a);}),_CD,_16H))),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(_16O),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};}else{return E(_VW);}}break;case 104:return {_:0,a:E(_16F),b:E(_16G),c:E(B(_16b(_16H))),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(_16O),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};case 106:var _17j=B(_Az(B(_o8(_VQ,_17a))));return (_17j._==0)?E(_VX):(E(_17j.b)._==0)?{_:0,a:E(_16F),b:E(_16G),c:E(_16H),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(_16O),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:E(_17j.a),q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178}:E(_VW);case 108:return {_:0,a:E(_16F),b:E(_16G),c:E(_16H),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(B(_VF(_16D,_16M))),i:E(B(_y(_16N,_179))),j:E(B(_VF(_16D,_16O))),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_ls),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};case 109:var _17k=B(_W7(B(_77(_16O,_16D)),_17a)),_17l=_17k.c,_17m=B(_hq(_17l,_10));if(!E(_17m)){var _17n=B(_Ww(_16D,new T2(0,new T(function(){return E(B(_77(_16M,_16D)).a);}),new T2(1,_17b,_17l)),_16M));}else{var _17n=B(_VF(_16D,_16M));}if(!E(_17m)){var _17o=B(_Ww(_16D,_17k.a,_16O));}else{var _17o=B(_VF(_16D,_16O));}return {_:0,a:E(_16F),b:E(_16G),c:E(_16H),d:_16I,e:_16J,f:_16K,g:E(B(_10w(_17k.b))),h:E(_17n),i:E(B(_y(_16N,_179))),j:E(_17o),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_ls),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};case 114:var _17p=B(_77(_10I,_16K));return {_:0,a:E(B(_77(_10S,_16K))),b:E(_17p),c:E(B(_Xh(_17p.a,E(_17p.b),new T(function(){return B(_77(_15W,_16K));})))),d:B(_77(_10V,_16K)),e:32,f:_16K,g:E(_16B),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(B(_jH(_16x,_16O))),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_ls),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};case 115:return {_:0,a:E(_16F),b:E(_16G),c:E(B(_16n(_16H))),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(_16O),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};case 116:var _17q=B(_77(_16O,_16D)),_17r=B(_W7(_17q,_17a)),_17s=E(_17r.a);if(!E(_17s)){var _17t=true;}else{var _17t=false;}if(!E(_17t)){var _17u=B(_Ww(_16D,_17s,_16O));}else{var _17u=B(_Ww(_16D,_17q+1|0,_16O));}if(!E(_17t)){var _17v=__Z;}else{var _17v=E(_17r.b);}if(!B(_hq(_17v,_10))){var _17w=B(_16C(_16D,_17v,_16F,_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_17u,_16P,_16Q,_16R,_16S,_16T,_16U,_16V,_16W,_16X,_16Y,_16Z,_170,_171,_172,_173,_174,_175,_176,_177,_178));return {_:0,a:E(_17w.a),b:E(_17w.b),c:E(_17w.c),d:_17w.d,e:_17w.e,f:_17w.f,g:E(_17w.g),h:E(_17w.h),i:E(B(_y(_16N,_179))),j:E(_17w.j),k:E(_17w.k),l:E(_17w.l),m:_17w.m,n:_17w.n,o:_17w.o,p:_17w.p,q:_17w.q,r:E(_17w.r),s:_17w.s,t:E(_17w.t),u:E(_17w.u),v:E(_17w.v),w:E(_17w.w),x:E(_17w.x),y:E(_17w.y),z:E(_17w.z),A:E(_17w.A),B:E(_17w.B),C:E(_17w.C),D:_17w.D};}else{return {_:0,a:E(_16F),b:E(_16G),c:E(_16H),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(_17u),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};}break;case 119:return {_:0,a:E(_10R),b:E(_10H),c:E(_16w),d:E(_16u),e:32,f:0,g:E(_16r),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(B(_jH(_16x,_16O))),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_ls),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};default:return {_:0,a:E(_16F),b:E(_16G),c:E(_16H),d:_16I,e:_16J,f:_16K,g:E(_16L),h:E(_16M),i:E(B(_y(_16N,_179))),j:E(_16O),k:E(_16P),l:E(_16Q),m:_16R,n:_16S,o:_16T,p:_16U,q:_16V,r:E(_16W),s:_16X,t:E(_16Y),u:E(_16Z),v:E(_170),w:E(_171),x:E(_172),y:E(_173),z:E(_174),A:E(_175),B:E(_176),C:E(_177),D:_178};}}},_17x=function(_17y,_17z,_17A,_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184){var _185=E(_17A);if(!_185._){return {_:0,a:_17B,b:_17C,c:_17D,d:_17E,e:_17F,f:_17G,g:_17H,h:_17I,i:_17J,j:_17K,k:_17L,l:_17M,m:_17N,n:_17O,o:_17P,p:_17Q,q:_17R,r:_17S,s:_17T,t:_17U,u:_17V,v:_17W,w:_17X,x:_17Y,y:_17Z,z:_180,A:_181,B:_182,C:_183,D:_184};}else{var _186=_185.b,_187=E(_185.a),_188=_187.a,_189=_187.b,_18a=function(_18b,_18c,_18d){var _18e=function(_18f,_18g){if(!B(_hq(_18f,_10))){var _18h=E(_18f);if(!_18h._){return E(_16t);}else{var _18i=_18h.b,_18j=E(_18h.a),_18k=function(_18l,_18m,_18n,_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x,_18y,_18z,_18A,_18B,_18C,_18D,_18E,_18F,_18G,_18H,_18I,_18J,_18K,_18L,_18M,_18N,_18O){if(B(_7a(_18u,0))!=B(_7a(_17K,0))){return {_:0,a:_18l,b:_18m,c:_18n,d:_18o,e:_18p,f:_18q,g:_18r,h:_18s,i:_18t,j:_18u,k:_18v,l:_18w,m:_18x,n:_18y,o:_18z,p:_18A,q:_18B,r:_18C,s:_18D,t:_18E,u:_18F,v:_18G,w:_18H,x:_18I,y:_18J,z:_18K,A:_18L,B:_18M,C:_18N,D:_18O};}else{return new F(function(){return _17x(new T(function(){return E(_17y)+1|0;}),_17z,_186,_18l,_18m,_18n,_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x,_18y,_18z,_18A,_18B,_18C,_18D,_18E,_18F,_18G,_18H,_18I,_18J,_18K,_18L,_18M,_18N,_18O);});}};switch(E(_18j)){case 97:var _18P=new T(function(){var _18Q=E(_18i);if(!_18Q._){return E(_16s);}else{return new T2(0,_18Q.a,_18Q.b);}}),_18R=new T(function(){var _18S=B(_Sn(E(_18P).b));return new T2(0,_18S.a,_18S.b);}),_18T=B(_Az(B(_o8(_VQ,new T(function(){return E(E(_18R).b);})))));if(!_18T._){return E(_VX);}else{if(!E(_18T.b)._){var _18U=new T(function(){var _18V=B(_Az(B(_o8(_VQ,new T(function(){return E(E(_18R).a);})))));if(!_18V._){return E(_VX);}else{if(!E(_18V.b)._){return E(_18V.a);}else{return E(_VW);}}},1);return new F(function(){return _18k(_17B,_17C,B(_ny(_18U,E(_18T.a),new T(function(){return E(E(_18P).a);}),_CD,_17D)),_17E,_17F,_17G,_17H,_17I,B(_y(_17J,_18h)),_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});}else{return E(_VW);}}break;case 104:return new F(function(){return _18k(_17B,_17C,B(_16b(_17D)),_17E,_17F,_17G,_17H,_17I,B(_y(_17J,_18h)),_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});break;case 106:var _18W=B(_Az(B(_o8(_VQ,_18i))));if(!_18W._){return E(_VX);}else{if(!E(_18W.b)._){return new F(function(){return _18k(_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,B(_y(_17J,_18h)),_17K,_17L,_17M,_17N,_17O,_17P,E(_18W.a),_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});}else{return E(_VW);}}break;case 108:var _18X=E(_18g);return new F(function(){return _18k(_17B,_17C,_17D,_17E,_17F,_17G,_17H,B(_VF(_18X,_17I)),B(_y(_17J,_18h)),B(_VF(_18X,_17K)),_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_ls,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});break;case 109:var _18Y=E(_18g),_18Z=B(_W7(B(_77(_17K,_18Y)),_18i)),_190=_18Z.c,_191=B(_hq(_190,_10));if(!E(_191)){var _192=B(_Ww(_18Y,new T2(0,new T(function(){return E(B(_77(_17I,_18Y)).a);}),new T2(1,_18j,_190)),_17I));}else{var _192=B(_VF(_18Y,_17I));}if(!E(_191)){var _193=B(_Ww(_18Y,_18Z.a,_17K));}else{var _193=B(_VF(_18Y,_17K));}return new F(function(){return _18k(_17B,_17C,_17D,_17E,_17F,_17G,B(_10w(_18Z.b)),_192,B(_y(_17J,_18h)),_193,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_ls,_17Y,_17Z,_180,_181,_182,_183,_184);});break;case 114:var _194=B(_77(_10I,_17G));return new F(function(){return _18k(B(_77(_10S,_17G)),_194,B(_Xh(_194.a,E(_194.b),new T(function(){return B(_77(_15W,_17G));}))),B(_77(_10V,_17G)),32,_17G,E(_16B),_17I,B(_y(_17J,_18h)),B(_jH(_16x,_17K)),_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_ls,_17Y,_17Z,_180,_181,_182,_183,_184);});break;case 115:return new F(function(){return _18k(_17B,_17C,B(_16n(_17D)),_17E,_17F,_17G,_17H,_17I,B(_y(_17J,_18h)),_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});break;case 116:var _195=E(_18g),_196=B(_77(_17K,_195)),_197=B(_W7(_196,_18i)),_198=E(_197.a);if(!E(_198)){var _199=true;}else{var _199=false;}if(!E(_199)){var _19a=B(_Ww(_195,_198,_17K));}else{var _19a=B(_Ww(_195,_196+1|0,_17K));}if(!E(_199)){var _19b=__Z;}else{var _19b=E(_197.b);}if(!B(_hq(_19b,_10))){var _19c=B(_16C(_195,_19b,_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,_17J,_19a,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184));return new F(function(){return _18k(_19c.a,_19c.b,_19c.c,_19c.d,_19c.e,_19c.f,_19c.g,_19c.h,B(_y(_17J,_18h)),_19c.j,_19c.k,_19c.l,_19c.m,_19c.n,_19c.o,_19c.p,_19c.q,_19c.r,_19c.s,_19c.t,_19c.u,_19c.v,_19c.w,_19c.x,_19c.y,_19c.z,_19c.A,_19c.B,_19c.C,_19c.D);});}else{return new F(function(){return _18k(_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,B(_y(_17J,_18h)),_19a,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});}break;case 119:return new F(function(){return _18k(_10R,_10H,E(_16w),E(_16u),32,0,E(_16r),_17I,B(_y(_17J,_18h)),B(_jH(_16x,_17K)),_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_ls,_17Y,_17Z,_180,_181,_182,_183,_184);});break;default:return new F(function(){return _18k(_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,B(_y(_17J,_18h)),_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});}}}else{return new F(function(){return _17x(new T(function(){return E(_17y)+1|0;}),_17z,_186,_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_180,_181,_182,_183,_184);});}},_19d=function(_19e){if(!B(_4B(_6f,_10U,_188))){return new T2(0,_189,_17y);}else{var _19f=function(_19g){while(1){var _19h=B((function(_19i){var _19j=E(_19i);if(!_19j._){return true;}else{var _19k=_19j.b,_19l=E(_19j.a);if(!_19l._){return E(_10T);}else{switch(E(_19l.a)){case 99:if(!E(_17U)){return false;}else{var _19m=function(_19n){while(1){var _19o=E(_19n);if(!_19o._){return true;}else{var _19p=_19o.b,_19q=E(_19o.a);if(!_19q._){return E(_10T);}else{if(E(_19q.a)==115){var _19r=B(_Az(B(_o8(_VQ,_19q.b))));if(!_19r._){return E(_VX);}else{if(!E(_19r.b)._){if(_17G!=E(_19r.a)){return false;}else{_19n=_19p;continue;}}else{return E(_VW);}}}else{_19n=_19p;continue;}}}}};return new F(function(){return _19m(_19k);});}break;case 115:var _19s=B(_Az(B(_o8(_VQ,_19l.b))));if(!_19s._){return E(_VX);}else{if(!E(_19s.b)._){if(_17G!=E(_19s.a)){return false;}else{_19g=_19k;return __continue;}}else{return E(_VW);}}break;default:_19g=_19k;return __continue;}}}})(_19g));if(_19h!=__continue){return _19h;}}};return (!B(_19f(_18d)))?new T2(0,_10,_17y):new T2(0,_189,_17y);}},_19t=B(_7a(_17z,0))-B(_7a(new T2(1,_18b,_18c),0))|0;if(_19t>0){var _19u=B(_Xy(_19t,_17z));}else{var _19u=E(_17z);}if(E(B(_Vn(_18b,_18c,_Fg)))==63){if(!B(_fh(_19u,_10))){var _19v=E(_19u);if(!_19v._){var _19w=E(_D2);}else{var _19w=B(_CX(_19v.a,_19v.b));}var _19x=_19w;}else{var _19x=E(_19u);}var _19y=_19x;}else{var _19y=E(_19u);}if(E(B(_Vv(_18b,_18c,_Fg)))==63){if(!B(_hq(B(_CX(_18b,_18c)),_19y))){return new F(function(){return _18e(_10,_17y);});}else{var _19z=B(_19d(_));return new F(function(){return _18e(_19z.a,_19z.b);});}}else{if(!B(_hq(new T2(1,_18b,_18c),_19y))){return new F(function(){return _18e(_10,_17y);});}else{var _19A=B(_19d(_));return new F(function(){return _18e(_19A.a,_19A.b);});}}},_19B=E(_188);if(!_19B._){return E(_Fg);}else{var _19C=_19B.a,_19D=E(_19B.b);if(!_19D._){return new F(function(){return _18a(_19C,_10,_10);});}else{var _19E=E(_19C),_19F=new T(function(){var _19G=B(_lz(38,_19D.a,_19D.b));return new T2(0,_19G.a,_19G.b);});if(E(_19E)==38){return E(_Fg);}else{return new F(function(){return _18a(_19E,new T(function(){return E(E(_19F).a);}),new T(function(){return E(E(_19F).b);}));});}}}}},_19H=function(_19I,_19J){var _19K=new T(function(){var _19L=B(_Az(B(_o8(_Qs,new T(function(){return B(_eH(3,B(_I(0,imul(E(_19J),E(_19I)-1|0)|0,_10))));})))));if(!_19L._){return E(_Qr);}else{if(!E(_19L.b)._){return E(_19L.a);}else{return E(_Qq);}}});return new T2(0,new T(function(){return B(_MF(_19K,_19I));}),_19K);},_19M=function(_19N){var _19O=E(_19N);if(!_19O._){return new T2(0,_10,_10);}else{var _19P=E(_19O.a),_19Q=new T(function(){var _19R=B(_19M(_19O.b));return new T2(0,_19R.a,_19R.b);});return new T2(0,new T2(1,_19P.a,new T(function(){return E(E(_19Q).a);})),new T2(1,_19P.b,new T(function(){return E(E(_19Q).b);})));}},_19S=function(_19T){var _19U=E(_19T);switch(_19U){case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;default:if(_19U>>>0>1114111){return new F(function(){return _sn(_19U);});}else{return _19U;}}},_19V=function(_19W,_19X){while(1){var _19Y=E(_19X);if(!_19Y._){return __Z;}else{var _19Z=_19Y.b,_1a0=E(_19W);if(_1a0==1){return E(_19Z);}else{_19W=_1a0-1|0;_19X=_19Z;continue;}}}},_1a1=function(_1a2,_1a3){while(1){var _1a4=E(_1a3);if(!_1a4._){return __Z;}else{var _1a5=_1a4.b,_1a6=E(_1a2);if(_1a6==1){return E(_1a5);}else{_1a2=_1a6-1|0;_1a3=_1a5;continue;}}}},_1a7=new T2(1,_5V,_10),_1a8=64,_1a9=new T2(1,_1a8,_10),_1aa=function(_1ab,_1ac){while(1){var _1ad=E(_1ab);if(!_1ad._){return E(_1ac);}else{_1ab=_1ad.b;_1ac=_1ad.a;continue;}}},_1ae=57,_1af=48,_1ag=new T2(1,_1a8,_10),_1ah=new T(function(){return B(err(_nZ));}),_1ai=new T(function(){return B(err(_nX));}),_1aj=new T(function(){return B(A3(_zS,_Al,_zn,_As));}),_1ak=function(_1al,_1am){if((_1am-48|0)>>>0>9){var _1an=_1am+_1al|0,_1ao=function(_1ap){if(!B(_4B(_6f,_1ap,_1ag))){return E(_1ap);}else{return new F(function(){return _1ak(_1al,_1ap);});}};if(_1an<=122){if(_1an>=97){if(_1an>>>0>1114111){return new F(function(){return _sn(_1an);});}else{return new F(function(){return _1ao(_1an);});}}else{if(_1an<=90){if(_1an>>>0>1114111){return new F(function(){return _sn(_1an);});}else{return new F(function(){return _1ao(_1an);});}}else{var _1aq=65+(_1an-90|0)|0;if(_1aq>>>0>1114111){return new F(function(){return _sn(_1aq);});}else{return new F(function(){return _1ao(_1aq);});}}}}else{var _1ar=97+(_1an-122|0)|0;if(_1ar>>>0>1114111){return new F(function(){return _sn(_1ar);});}else{return new F(function(){return _1ao(_1ar);});}}}else{var _1as=B(_Az(B(_o8(_1aj,new T2(1,_1am,_10)))));if(!_1as._){return E(_1ai);}else{if(!E(_1as.b)._){var _1at=E(_1as.a)+_1al|0;switch(_1at){case  -1:return E(_1af);case 10:return E(_1ae);default:return new F(function(){return _1aa(B(_I(0,_1at,_10)),_Fg);});}}else{return E(_1ah);}}}},_1au=function(_1av,_1aw){if((_1av-48|0)>>>0>9){return _1aw;}else{var _1ax=B(_Az(B(_o8(_1aj,new T2(1,_1av,_10)))));if(!_1ax._){return E(_1ai);}else{if(!E(_1ax.b)._){return new F(function(){return _1ak(E(_1ax.a),_1aw);});}else{return E(_1ah);}}}},_1ay=function(_1az,_1aA){return new F(function(){return _1au(E(_1az),E(_1aA));});},_1aB=new T2(1,_1ay,_10),_1aC=5,_1aD=new T2(1,_1aC,_10),_1aE=function(_1aF,_1aG){return new F(function(){return _77(_1aF,E(_1aG));});},_1aH=function(_1aI,_1aJ,_1aK,_1aL){return (!B(_hq(_1aI,_1aK)))?true:(!B(_8f(_1aJ,_1aL)))?true:false;},_1aM=function(_1aN,_1aO){var _1aP=E(_1aN),_1aQ=E(_1aO);return new F(function(){return _1aH(_1aP.a,_1aP.b,_1aQ.a,_1aQ.b);});},_1aR=function(_1aS,_1aT,_1aU,_1aV){if(!B(_hq(_1aS,_1aU))){return false;}else{return new F(function(){return _8f(_1aT,_1aV);});}},_1aW=function(_1aX,_1aY){var _1aZ=E(_1aX),_1b0=E(_1aY);return new F(function(){return _1aR(_1aZ.a,_1aZ.b,_1b0.a,_1b0.b);});},_1b1=new T2(0,_1aW,_1aM),_1b2=function(_1b3){var _1b4=E(_1b3);if(!_1b4._){return new T2(0,_10,_10);}else{var _1b5=E(_1b4.a),_1b6=new T(function(){var _1b7=B(_1b2(_1b4.b));return new T2(0,_1b7.a,_1b7.b);});return new T2(0,new T2(1,_1b5.a,new T(function(){return E(E(_1b6).a);})),new T2(1,_1b5.b,new T(function(){return E(E(_1b6).b);})));}},_1b8=function(_1b9){var _1ba=E(_1b9);if(!_1ba._){return new T2(0,_10,_10);}else{var _1bb=E(_1ba.a),_1bc=new T(function(){var _1bd=B(_1b8(_1ba.b));return new T2(0,_1bd.a,_1bd.b);});return new T2(0,new T2(1,_1bb.a,new T(function(){return E(E(_1bc).a);})),new T2(1,_1bb.b,new T(function(){return E(E(_1bc).b);})));}},_1be=function(_1bf){var _1bg=E(_1bf);if(!_1bg._){return new T2(0,_10,_10);}else{var _1bh=E(_1bg.a),_1bi=new T(function(){var _1bj=B(_1be(_1bg.b));return new T2(0,_1bj.a,_1bj.b);});return new T2(0,new T2(1,_1bh.a,new T(function(){return E(E(_1bi).a);})),new T2(1,_1bh.b,new T(function(){return E(E(_1bi).b);})));}},_1bk=function(_1bl,_1bm){return (_1bl<=_1bm)?new T2(1,_1bl,new T(function(){return B(_1bk(_1bl+1|0,_1bm));})):__Z;},_1bn=new T(function(){return B(_1bk(65,90));}),_1bo=function(_1bp){return (_1bp<=122)?new T2(1,_1bp,new T(function(){return B(_1bo(_1bp+1|0));})):E(_1bn);},_1bq=new T(function(){return B(_1bo(97));}),_1br=function(_1bs){while(1){var _1bt=E(_1bs);if(!_1bt._){return true;}else{if(!B(_4B(_6f,_1bt.a,_1bq))){return false;}else{_1bs=_1bt.b;continue;}}}},_1bu=new T(function(){return B(err(_nX));}),_1bv=new T(function(){return B(err(_nZ));}),_1bw=new T(function(){return B(A3(_Uc,_Ux,_zn,_As));}),_1bx=new T2(0,_10,_10),_1by=new T1(0,0),_1bz=new T1(0,2),_1bA=new T1(0,1),_1bB=new T2(0,_10,_1by),_1bC=function(_1bD,_1bE,_1bF){var _1bG=new T(function(){var _1bH=B(_1b2(_1bE));return new T2(0,_1bH.a,_1bH.b);}),_1bI=new T(function(){return E(E(_1bG).b);}),_1bJ=new T(function(){var _1bK=B(_1b8(E(_1bG).a));return new T2(0,_1bK.a,_1bK.b);}),_1bL=new T(function(){return E(E(_1bJ).b);}),_1bM=new T(function(){return E(E(_1bJ).a);}),_1bN=function(_1bO){while(1){var _1bP=B((function(_1bQ){var _1bR=E(_1bQ);if(!_1bR._){return __Z;}else{var _1bS=_1bR.b,_1bT=new T(function(){return E(B(_1be(_1bR.a)).a);}),_1bU=new T(function(){return B(_4B(_6f,_RR,_1bT));}),_1bV=new T(function(){if(!E(_1bU)){return E(_1bx);}else{var _1bW=B(_Sn(_1bT));return new T2(0,_1bW.a,_1bW.b);}}),_1bX=new T(function(){return E(E(_1bV).a);}),_1bY=new T(function(){return B(_jf(_fp,_1bX,_1bM));});if(!B(_4B(_fp,_1bX,_1bM))){var _1bZ=false;}else{var _1bZ=B(_77(_1bI,E(_1bY)))==E(_1bD);}var _1c0=new T(function(){return E(E(_1bV).b);}),_1c1=new T(function(){return B(_jf(_fp,_1c0,_1bM));}),_1c2=new T(function(){if(!B(_4B(_fp,_1c0,_1bM))){return false;}else{return B(_77(_1bI,E(_1c1)))==E(_1bD);}}),_1c3=function(_1c4){var _1c5=function(_1c6){return (!E(_1bZ))?__Z:(!E(_1c2))?__Z:new T2(1,new T2(0,_1bX,new T(function(){return B(_1aE(_1bL,_1bY));})),new T2(1,new T2(0,_1c0,new T(function(){return B(_1aE(_1bL,_1c1));})),_10));};if(!E(_1bZ)){if(!E(_1c2)){return new F(function(){return _1c5(_);});}else{return new T2(1,new T2(0,_1c0,new T(function(){return B(_1aE(_1bL,_1c1));})),_10);}}else{return new F(function(){return _1c5(_);});}};if(!E(_1bZ)){var _1c7=B(_1c3(_));}else{if(!E(_1c2)){var _1c8=new T2(1,new T2(0,_1bX,new T(function(){return B(_1aE(_1bL,_1bY));})),_10);}else{var _1c8=B(_1c3(_));}var _1c7=_1c8;}if(!B(_6g(_1b1,_1c7,_10))){return new F(function(){return _y(_1c7,new T(function(){return B(_1bN(_1bS));},1));});}else{if(!E(_1bU)){_1bO=_1bS;return __continue;}else{var _1c9=new T(function(){if(!E(_1bZ)){return E(_1c2);}else{return true;}}),_1ca=function(_1cb){return (!B(_1br(_1c0)))?E(_1by):(!E(_1c9))?(!B(_fh(_1bX,_10)))?(!B(_U7(_1bX)))?E(_1by):E(_1bz):E(_1by):E(_1by);};if(!B(_1br(_1bX))){var _1cc=B(_1ca(_));}else{if(!E(_1c9)){if(!B(_fh(_1c0,_10))){if(!B(_U7(_1c0))){var _1cd=B(_1ca(_));}else{var _1cd=E(_1bA);}var _1ce=_1cd;}else{var _1ce=B(_1ca(_));}var _1cf=_1ce;}else{var _1cf=B(_1ca(_));}var _1cc=_1cf;}if(!B(_8T(_1cc,_1by))){_1bO=_1bS;return __continue;}else{var _1cg=new T(function(){if(!B(_8f(_1cc,_1bA))){if(!B(_8f(_1cc,_1bz))){return E(_1bB);}else{return new T2(0,_1c0,new T(function(){var _1ch=B(_Az(B(_o8(_1bw,_1bX))));if(!_1ch._){return E(_1bu);}else{if(!E(_1ch.b)._){return E(_1ch.a);}else{return E(_1bv);}}}));}}else{return new T2(0,_1bX,new T(function(){var _1ci=B(_Az(B(_o8(_1bw,_1c0))));if(!_1ci._){return E(_1bu);}else{if(!E(_1ci.b)._){return E(_1ci.a);}else{return E(_1bv);}}}));}});return new T2(1,_1cg,new T(function(){return B(_1bN(_1bS));}));}}}}})(_1bO));if(_1bP!=__continue){return _1bP;}}};return new F(function(){return _1bN(_1bF);});},_1cj=new T(function(){return B(_a2("Grid.hs:(21,1)-(28,56)|function checkGrid"));}),_1ck=function(_1cl,_1cm){while(1){var _1cn=E(_1cm);if(!_1cn._){return false;}else{var _1co=_1cn.b,_1cp=E(_1cl),_1cq=_1cp.a,_1cr=_1cp.b,_1cs=E(_1cn.a);if(!_1cs._){return E(_1cj);}else{var _1ct=E(_1cs.a),_1cu=_1ct.a,_1cv=_1ct.b,_1cw=E(_1cs.b);if(!_1cw._){var _1cx=E(_1cq),_1cy=E(_1cx);if(_1cy==32){switch(E(_1cr)){case 0:if(!E(_1cv)){return true;}else{_1cl=new T2(0,_1cx,_CD);_1cm=_1co;continue;}break;case 1:if(E(_1cv)==1){return true;}else{_1cl=new T2(0,_1cx,_10X);_1cm=_1co;continue;}break;case 2:if(E(_1cv)==2){return true;}else{_1cl=new T2(0,_1cx,_11O);_1cm=_1co;continue;}break;case 3:if(E(_1cv)==3){return true;}else{_1cl=new T2(0,_1cx,_126);_1cm=_1co;continue;}break;case 4:if(E(_1cv)==4){return true;}else{_1cl=new T2(0,_1cx,_160);_1cm=_1co;continue;}break;case 5:if(E(_1cv)==5){return true;}else{_1cl=new T2(0,_1cx,_161);_1cm=_1co;continue;}break;case 6:if(E(_1cv)==6){return true;}else{_1cl=new T2(0,_1cx,_15X);_1cm=_1co;continue;}break;case 7:if(E(_1cv)==7){return true;}else{_1cl=new T2(0,_1cx,_15Y);_1cm=_1co;continue;}break;default:if(E(_1cv)==8){return true;}else{_1cl=new T2(0,_1cx,_15Z);_1cm=_1co;continue;}}}else{if(_1cy!=E(_1cu)){_1cl=_1cp;_1cm=_1co;continue;}else{switch(E(_1cr)){case 0:if(!E(_1cv)){return true;}else{_1cl=new T2(0,_1cx,_CD);_1cm=_1co;continue;}break;case 1:if(E(_1cv)==1){return true;}else{_1cl=new T2(0,_1cx,_10X);_1cm=_1co;continue;}break;case 2:if(E(_1cv)==2){return true;}else{_1cl=new T2(0,_1cx,_11O);_1cm=_1co;continue;}break;case 3:if(E(_1cv)==3){return true;}else{_1cl=new T2(0,_1cx,_126);_1cm=_1co;continue;}break;case 4:if(E(_1cv)==4){return true;}else{_1cl=new T2(0,_1cx,_160);_1cm=_1co;continue;}break;case 5:if(E(_1cv)==5){return true;}else{_1cl=new T2(0,_1cx,_161);_1cm=_1co;continue;}break;case 6:if(E(_1cv)==6){return true;}else{_1cl=new T2(0,_1cx,_15X);_1cm=_1co;continue;}break;case 7:if(E(_1cv)==7){return true;}else{_1cl=new T2(0,_1cx,_15Y);_1cm=_1co;continue;}break;default:if(E(_1cv)==8){return true;}else{_1cl=new T2(0,_1cx,_15Z);_1cm=_1co;continue;}}}}}else{var _1cz=E(_1cq),_1cA=E(_1cz);if(_1cA==32){switch(E(_1cr)){case 0:if(!E(_1cv)){return true;}else{_1cl=new T2(0,_1cz,_CD);_1cm=new T2(1,_1cw,_1co);continue;}break;case 1:if(E(_1cv)==1){return true;}else{_1cl=new T2(0,_1cz,_10X);_1cm=new T2(1,_1cw,_1co);continue;}break;case 2:if(E(_1cv)==2){return true;}else{_1cl=new T2(0,_1cz,_11O);_1cm=new T2(1,_1cw,_1co);continue;}break;case 3:if(E(_1cv)==3){return true;}else{_1cl=new T2(0,_1cz,_126);_1cm=new T2(1,_1cw,_1co);continue;}break;case 4:if(E(_1cv)==4){return true;}else{_1cl=new T2(0,_1cz,_160);_1cm=new T2(1,_1cw,_1co);continue;}break;case 5:if(E(_1cv)==5){return true;}else{_1cl=new T2(0,_1cz,_161);_1cm=new T2(1,_1cw,_1co);continue;}break;case 6:if(E(_1cv)==6){return true;}else{_1cl=new T2(0,_1cz,_15X);_1cm=new T2(1,_1cw,_1co);continue;}break;case 7:if(E(_1cv)==7){return true;}else{_1cl=new T2(0,_1cz,_15Y);_1cm=new T2(1,_1cw,_1co);continue;}break;default:if(E(_1cv)==8){return true;}else{_1cl=new T2(0,_1cz,_15Z);_1cm=new T2(1,_1cw,_1co);continue;}}}else{if(_1cA!=E(_1cu)){_1cl=_1cp;_1cm=new T2(1,_1cw,_1co);continue;}else{switch(E(_1cr)){case 0:if(!E(_1cv)){return true;}else{_1cl=new T2(0,_1cz,_CD);_1cm=new T2(1,_1cw,_1co);continue;}break;case 1:if(E(_1cv)==1){return true;}else{_1cl=new T2(0,_1cz,_10X);_1cm=new T2(1,_1cw,_1co);continue;}break;case 2:if(E(_1cv)==2){return true;}else{_1cl=new T2(0,_1cz,_11O);_1cm=new T2(1,_1cw,_1co);continue;}break;case 3:if(E(_1cv)==3){return true;}else{_1cl=new T2(0,_1cz,_126);_1cm=new T2(1,_1cw,_1co);continue;}break;case 4:if(E(_1cv)==4){return true;}else{_1cl=new T2(0,_1cz,_160);_1cm=new T2(1,_1cw,_1co);continue;}break;case 5:if(E(_1cv)==5){return true;}else{_1cl=new T2(0,_1cz,_161);_1cm=new T2(1,_1cw,_1co);continue;}break;case 6:if(E(_1cv)==6){return true;}else{_1cl=new T2(0,_1cz,_15X);_1cm=new T2(1,_1cw,_1co);continue;}break;case 7:if(E(_1cv)==7){return true;}else{_1cl=new T2(0,_1cz,_15Y);_1cm=new T2(1,_1cw,_1co);continue;}break;default:if(E(_1cv)==8){return true;}else{_1cl=new T2(0,_1cz,_15Z);_1cm=new T2(1,_1cw,_1co);continue;}}}}}}}}},_1cB=new T(function(){return B(unCStr("foldr1"));}),_1cC=new T(function(){return B(_dG(_1cB));}),_1cD=function(_1cE,_1cF){var _1cG=E(_1cF);if(!_1cG._){return E(_1cC);}else{var _1cH=_1cG.a,_1cI=E(_1cG.b);if(!_1cI._){return E(_1cH);}else{return new F(function(){return A2(_1cE,_1cH,new T(function(){return B(_1cD(_1cE,_1cI));}));});}}},_1cJ=new T(function(){return B(unCStr("\n"));}),_1cK=function(_1cL,_1cM,_){var _1cN=jsWriteHandle(E(_1cL),toJSStr(E(_1cM)));return _7f;},_1cO=function(_1cP,_1cQ,_){var _1cR=E(_1cP),_1cS=jsWriteHandle(_1cR,toJSStr(E(_1cQ)));return new F(function(){return _1cK(_1cR,_1cJ,_);});},_1cT=new T1(0,1002),_1cU=new T(function(){return B(unCStr("0.04"));}),_1cV=new T2(0,_1cU,_1cT),_1cW=new T2(0,_1cV,_10Q),_1cX=new T1(0,1000),_1cY=new T(function(){return B(unCStr("COVID19"));}),_1cZ=new T2(0,_1cY,_1cX),_1d0=new T2(0,_1cZ,_10P),_1d1=new T(function(){return B(unCStr("/P"));}),_1d2=new T2(0,_1d1,_1cX),_1d3=new T2(0,_1d2,_10P),_1d4=new T1(0,1001),_1d5=new T(function(){return B(unCStr("POSITIVE"));}),_1d6=new T2(0,_1d5,_1d4),_1d7=new T2(0,_1d6,_10P),_1d8=new T1(0,1003),_1d9=new T(function(){return B(unCStr("N"));}),_1da=new T2(0,_1d9,_1d8),_1db=new T2(0,_1da,_10P),_1dc=new T2(1,_1db,_10),_1dd=new T(function(){return B(unCStr("CONTACT"));}),_1de=new T2(0,_1dd,_1d8),_1df=new T2(0,_1de,_10P),_1dg=new T2(1,_1df,_1dc),_1dh=new T(function(){return B(unCStr("H"));}),_1di=new T2(0,_1dh,_1cT),_1dj=new T2(0,_1di,_10P),_1dk=new T2(1,_1dj,_1dg),_1dl=new T(function(){return B(unCStr("VACCINE"));}),_1dm=new T2(0,_1dl,_1cT),_1dn=new T2(0,_1dm,_10P),_1do=new T2(1,_1dn,_1dk),_1dp=new T(function(){return B(unCStr("MASK"));}),_1dq=new T2(0,_1dp,_1cT),_1dr=new T2(0,_1dq,_10P),_1ds=new T2(1,_1dr,_1do),_1dt=new T(function(){return B(unCStr("/I"));}),_1du=new T2(0,_1dt,_1d4),_1dv=new T2(0,_1du,_10P),_1dw=new T2(1,_1dv,_1ds),_1dx=new T2(1,_1d7,_1dw),_1dy=new T2(1,_1d3,_1dx),_1dz=new T2(1,_1d0,_1dy),_1dA=new T2(1,_1cW,_1dz),_1dB=new T(function(){return B(unCStr("Q3"));}),_1dC=new T2(0,_1dB,_1cT),_1dD=new T2(0,_1dC,_10Q),_1dE=new T2(1,_1dD,_1dA),_1dF=new T(function(){return B(unCStr("O"));}),_1dG=new T2(0,_1dF,_1d4),_1dH=new T2(0,_1dG,_10Q),_1dI=new T2(1,_1dH,_1dE),_1dJ=new T(function(){return B(unCStr("Q2"));}),_1dK=new T2(0,_1dJ,_1d4),_1dL=new T2(0,_1dK,_10Q),_1dM=new T2(1,_1dL,_1dI),_1dN=new T(function(){return B(unCStr("H2O"));}),_1dO=new T2(0,_1dN,_1cX),_1dP=new T2(0,_1dO,_10Q),_1dQ=new T2(1,_1dP,_1dM),_1dR=new T(function(){return B(unCStr("Q1"));}),_1dS=new T2(0,_1dR,_1cX),_1dT=new T2(0,_1dS,_10Q),_1dU=new T2(1,_1dT,_1dQ),_1dV=0,_1dW=new T(function(){return B(_Xh(_10G,5,_11L));}),_1dX=new T(function(){return B(_77(_em,1));}),_1dY= -1,_1dZ= -2,_1e0=new T(function(){return B(unCStr("I spent a special week"));}),_1e1=14,_1e2=4,_1e3=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1e4=10,_1e5=3,_1e6=new T(function(){return B(unCStr("Coding : yokoP"));}),_1e7=8,_1e8=new T(function(){return B(unCStr("Congratulations!"));}),_1e9=32,_1ea=new T2(0,_1e9,_161),_1eb=99,_1ec=64,_1ed=new T(function(){return B(_7a(_15W,0));}),_1ee=new T(function(){return B(_77(_em,2));}),_1ef=new T(function(){return B(unCStr("=="));}),_1eg=111,_1eh=112,_1ei=101,_1ej=102,_1ek=new T(function(){var _1el=E(_10V);if(!_1el._){return E(_dJ);}else{return E(_1el.a);}}),_1em=118,_1en=110,_1eo=98,_1ep=117,_1eq=new T(function(){return B(_a2("CvLoop.hs:(129,9)-(144,75)|function wnMove\'"));}),_1er=new T(function(){return B(_a2("CvLoop.hs:(114,17)-(118,70)|case"));}),_1es=new T(function(){return B(unCStr("Thank you for playing!"));}),_1et=new T(function(){return B(unCStr("choice"));}),_1eu=34,_1ev=new T2(1,_1eu,_10),_1ew=new T(function(){return B(unCStr("ACK"));}),_1ex=new T(function(){return B(unCStr("BEL"));}),_1ey=new T(function(){return B(unCStr("BS"));}),_1ez=new T(function(){return B(unCStr("SP"));}),_1eA=new T2(1,_1ez,_10),_1eB=new T(function(){return B(unCStr("US"));}),_1eC=new T2(1,_1eB,_1eA),_1eD=new T(function(){return B(unCStr("RS"));}),_1eE=new T2(1,_1eD,_1eC),_1eF=new T(function(){return B(unCStr("GS"));}),_1eG=new T2(1,_1eF,_1eE),_1eH=new T(function(){return B(unCStr("FS"));}),_1eI=new T2(1,_1eH,_1eG),_1eJ=new T(function(){return B(unCStr("ESC"));}),_1eK=new T2(1,_1eJ,_1eI),_1eL=new T(function(){return B(unCStr("SUB"));}),_1eM=new T2(1,_1eL,_1eK),_1eN=new T(function(){return B(unCStr("EM"));}),_1eO=new T2(1,_1eN,_1eM),_1eP=new T(function(){return B(unCStr("CAN"));}),_1eQ=new T2(1,_1eP,_1eO),_1eR=new T(function(){return B(unCStr("ETB"));}),_1eS=new T2(1,_1eR,_1eQ),_1eT=new T(function(){return B(unCStr("SYN"));}),_1eU=new T2(1,_1eT,_1eS),_1eV=new T(function(){return B(unCStr("NAK"));}),_1eW=new T2(1,_1eV,_1eU),_1eX=new T(function(){return B(unCStr("DC4"));}),_1eY=new T2(1,_1eX,_1eW),_1eZ=new T(function(){return B(unCStr("DC3"));}),_1f0=new T2(1,_1eZ,_1eY),_1f1=new T(function(){return B(unCStr("DC2"));}),_1f2=new T2(1,_1f1,_1f0),_1f3=new T(function(){return B(unCStr("DC1"));}),_1f4=new T2(1,_1f3,_1f2),_1f5=new T(function(){return B(unCStr("DLE"));}),_1f6=new T2(1,_1f5,_1f4),_1f7=new T(function(){return B(unCStr("SI"));}),_1f8=new T2(1,_1f7,_1f6),_1f9=new T(function(){return B(unCStr("SO"));}),_1fa=new T2(1,_1f9,_1f8),_1fb=new T(function(){return B(unCStr("CR"));}),_1fc=new T2(1,_1fb,_1fa),_1fd=new T(function(){return B(unCStr("FF"));}),_1fe=new T2(1,_1fd,_1fc),_1ff=new T(function(){return B(unCStr("VT"));}),_1fg=new T2(1,_1ff,_1fe),_1fh=new T(function(){return B(unCStr("LF"));}),_1fi=new T2(1,_1fh,_1fg),_1fj=new T(function(){return B(unCStr("HT"));}),_1fk=new T2(1,_1fj,_1fi),_1fl=new T2(1,_1ey,_1fk),_1fm=new T2(1,_1ex,_1fl),_1fn=new T2(1,_1ew,_1fm),_1fo=new T(function(){return B(unCStr("ENQ"));}),_1fp=new T2(1,_1fo,_1fn),_1fq=new T(function(){return B(unCStr("EOT"));}),_1fr=new T2(1,_1fq,_1fp),_1fs=new T(function(){return B(unCStr("ETX"));}),_1ft=new T2(1,_1fs,_1fr),_1fu=new T(function(){return B(unCStr("STX"));}),_1fv=new T2(1,_1fu,_1ft),_1fw=new T(function(){return B(unCStr("SOH"));}),_1fx=new T2(1,_1fw,_1fv),_1fy=new T(function(){return B(unCStr("NUL"));}),_1fz=new T2(1,_1fy,_1fx),_1fA=92,_1fB=new T(function(){return B(unCStr("\\DEL"));}),_1fC=new T(function(){return B(unCStr("\\a"));}),_1fD=new T(function(){return B(unCStr("\\\\"));}),_1fE=new T(function(){return B(unCStr("\\SO"));}),_1fF=new T(function(){return B(unCStr("\\r"));}),_1fG=new T(function(){return B(unCStr("\\f"));}),_1fH=new T(function(){return B(unCStr("\\v"));}),_1fI=new T(function(){return B(unCStr("\\n"));}),_1fJ=new T(function(){return B(unCStr("\\t"));}),_1fK=new T(function(){return B(unCStr("\\b"));}),_1fL=function(_1fM,_1fN){if(_1fM<=127){var _1fO=E(_1fM);switch(_1fO){case 92:return new F(function(){return _y(_1fD,_1fN);});break;case 127:return new F(function(){return _y(_1fB,_1fN);});break;default:if(_1fO<32){var _1fP=E(_1fO);switch(_1fP){case 7:return new F(function(){return _y(_1fC,_1fN);});break;case 8:return new F(function(){return _y(_1fK,_1fN);});break;case 9:return new F(function(){return _y(_1fJ,_1fN);});break;case 10:return new F(function(){return _y(_1fI,_1fN);});break;case 11:return new F(function(){return _y(_1fH,_1fN);});break;case 12:return new F(function(){return _y(_1fG,_1fN);});break;case 13:return new F(function(){return _y(_1fF,_1fN);});break;case 14:return new F(function(){return _y(_1fE,new T(function(){var _1fQ=E(_1fN);if(!_1fQ._){return __Z;}else{if(E(_1fQ.a)==72){return B(unAppCStr("\\&",_1fQ));}else{return E(_1fQ);}}},1));});break;default:return new F(function(){return _y(new T2(1,_1fA,new T(function(){return B(_77(_1fz,_1fP));})),_1fN);});}}else{return new T2(1,_1fO,_1fN);}}}else{var _1fR=new T(function(){var _1fS=jsShowI(_1fM);return B(_y(fromJSStr(_1fS),new T(function(){var _1fT=E(_1fN);if(!_1fT._){return __Z;}else{var _1fU=E(_1fT.a);if(_1fU<48){return E(_1fT);}else{if(_1fU>57){return E(_1fT);}else{return B(unAppCStr("\\&",_1fT));}}}},1)));});return new T2(1,_1fA,_1fR);}},_1fV=new T(function(){return B(unCStr("\\\""));}),_1fW=function(_1fX,_1fY){var _1fZ=E(_1fX);if(!_1fZ._){return E(_1fY);}else{var _1g0=_1fZ.b,_1g1=E(_1fZ.a);if(_1g1==34){return new F(function(){return _y(_1fV,new T(function(){return B(_1fW(_1g0,_1fY));},1));});}else{return new F(function(){return _1fL(_1g1,new T(function(){return B(_1fW(_1g0,_1fY));}));});}}},_1g2=new T(function(){return B(_1fW(_1et,_1ev));}),_1g3=new T2(1,_1eu,_1g2),_1g4=new T(function(){return B(unAppCStr("[]",_10));}),_1g5=new T2(1,_1eu,_10),_1g6=17,_1g7=2,_1g8=new T(function(){return B(unCStr("10/18 to 10/25 in 2021"));}),_1g9=15,_1ga=5,_1gb=new T2(1,_2B,_10),_1gc=function(_1gd,_1ge){return new T2(1,_1eu,new T(function(){return B(_1fW(_1gd,new T2(1,_1eu,_1ge)));}));},_1gf=function(_1gg){var _1gh=E(_1gg);if(!_1gh._){return E(_1gb);}else{var _1gi=new T(function(){var _1gj=E(_1gh.a),_1gk=new T(function(){return B(A3(_1cD,_6m,new T2(1,function(_1gl){return new F(function(){return _1gc(_1gj.a,_1gl);});},new T2(1,function(_1gm){return new F(function(){return _1gc(_1gj.b,_1gm);});},_10)),new T2(1,_G,new T(function(){return B(_1gf(_1gh.b));}))));});return new T2(1,_H,_1gk);});return new T2(1,_2A,_1gi);}},_1gn=function(_1go){var _1gp=E(_1go);if(!_1gp._){return E(_1gb);}else{var _1gq=new T(function(){return B(_I(0,E(_1gp.a),new T(function(){return B(_1gn(_1gp.b));})));});return new T2(1,_2A,_1gq);}},_1gr=function(_1gs){var _1gt=E(_1gs);if(!_1gt._){return E(_1gb);}else{var _1gu=new T(function(){var _1gv=E(_1gt.a),_1gw=new T(function(){return B(A3(_1cD,_6m,new T2(1,function(_1gx){return new F(function(){return _1gc(_1gv.a,_1gx);});},new T2(1,function(_1gy){return new F(function(){return _1gc(_1gv.b,_1gy);});},_10)),new T2(1,_G,new T(function(){return B(_1gr(_1gt.b));}))));});return new T2(1,_H,_1gw);});return new T2(1,_2A,_1gu);}},_1gz=new T(function(){return B(unCStr("True"));}),_1gA=new T(function(){return B(unCStr("False"));}),_1gB=function(_){return new F(function(){return jsMkStdout();});},_1gC=new T(function(){return B(_3(_1gB));}),_1gD=function(_1gE,_1gF,_1gG,_1gH,_1gI,_1gJ,_1gK,_1gL,_1gM,_1gN,_1gO,_1gP,_1gQ,_1gR,_1gS,_1gT,_1gU,_1gV,_1gW,_1gX,_1gY,_1gZ,_1h0,_1h1,_1h2,_1h3,_1h4,_1h5,_1h6,_1h7,_1h8,_1h9,_1ha,_1hb,_1hc,_){var _1hd=new T2(0,_1gT,_1gU),_1he=new T2(0,_1gI,_1gJ),_1hf=new T2(0,_1gG,_1gH);if(!E(_1h8)){var _1hg=function(_1hh){if(!E(_1h6)){var _1hi=function(_){var _1hj=function(_){var _1hk=function(_){var _1hl=B(_1cO(_1gC,new T2(1,_1eu,new T(function(){return B(_1fW(_1gQ,_1g5));})),_)),_1hm=function(_){var _1hn=function(_){var _1ho=B(_Rs(_1ga,_1gZ,_)),_1hp=E(_1ho).b,_1hq=E(_1gE),_1hr=_1hq.a,_1hs=_1hq.b,_1ht=new T(function(){return B(_19S(E(_1gF)));}),_1hu=new T(function(){var _1hv=function(_1hw,_1hx){var _1hy=E(_1hw),_1hz=B(_77(B(_77(_1gK,_1hx)),_1hy)),_1hA=_1hz.a,_1hB=_1hz.b;if(E(_1gM)==32){if(!B(_4B(_6f,_1hA,_1a9))){var _1hC=false;}else{switch(E(_1hB)){case 0:var _1hD=true;break;case 1:var _1hD=false;break;case 2:var _1hD=false;break;case 3:var _1hD=false;break;case 4:var _1hD=false;break;case 5:var _1hD=false;break;case 6:var _1hD=false;break;case 7:var _1hD=false;break;default:var _1hD=false;}var _1hC=_1hD;}var _1hE=_1hC;}else{var _1hE=false;}if(E(_1gM)==32){if(E(_1hA)==32){var _1hF=false;}else{switch(E(_1hB)){case 0:if(!E(_1hE)){var _1hG=true;}else{var _1hG=false;}var _1hH=_1hG;break;case 1:var _1hH=false;break;case 2:var _1hH=false;break;case 3:var _1hH=false;break;case 4:var _1hH=false;break;case 5:var _1hH=false;break;case 6:var _1hH=false;break;case 7:var _1hH=false;break;default:if(!E(_1hE)){var _1hI=true;}else{var _1hI=false;}var _1hH=_1hI;}var _1hF=_1hH;}var _1hJ=_1hF;}else{var _1hJ=false;}var _1hK=new T(function(){return B(_ny(_1hy,_1hx,new T(function(){if(!E(_1hJ)){if(!E(_1hE)){return E(_1hA);}else{return _1gL;}}else{return E(_1e9);}}),_1hB,_1gK));});switch(E(_1hB)){case 3:var _1hL=true;break;case 4:if(E(_1gM)==32){var _1hM=true;}else{var _1hM=false;}var _1hL=_1hM;break;default:var _1hL=false;}if(!E(_1hL)){var _1hN=E(_1hK);}else{var _1hO=E(_1gG),_1hP=new T(function(){return B(_77(_1hK,_1hx));}),_1hQ=function(_1hR,_1hS){var _1hT=E(_1hR);if(_1hT==( -1)){return E(_1hK);}else{var _1hU=new T(function(){return B(_ny(_1hy,_1hx,_1e9,_CD,_1hK));}),_1hV=E(_1hS);if(_1hV==( -1)){var _1hW=__Z;}else{var _1hW=B(_77(_1hU,_1hV));}if(E(B(_77(_1hW,_1hT)).a)==32){var _1hX=new T(function(){var _1hY=new T(function(){return B(_77(_1hP,_1hy));}),_1hZ=new T2(1,new T2(0,new T(function(){return E(E(_1hY).a);}),new T(function(){return E(E(_1hY).b);})),new T(function(){var _1i0=_1hT+1|0;if(_1i0>0){return B(_19V(_1i0,_1hW));}else{return E(_1hW);}}));if(0>=_1hT){return E(_1hZ);}else{var _1i1=function(_1i2,_1i3){var _1i4=E(_1i2);if(!_1i4._){return E(_1hZ);}else{var _1i5=_1i4.a,_1i6=E(_1i3);return (_1i6==1)?new T2(1,_1i5,_1hZ):new T2(1,_1i5,new T(function(){return B(_1i1(_1i4.b,_1i6-1|0));}));}};return B(_1i1(_1hW,_1hT));}}),_1i7=new T2(1,_1hX,new T(function(){var _1i8=_1hS+1|0;if(_1i8>0){return B(_1a1(_1i8,_1hU));}else{return E(_1hU);}}));if(0>=_1hS){return E(_1i7);}else{var _1i9=function(_1ia,_1ib){var _1ic=E(_1ia);if(!_1ic._){return E(_1i7);}else{var _1id=_1ic.a,_1ie=E(_1ib);return (_1ie==1)?new T2(1,_1id,_1i7):new T2(1,_1id,new T(function(){return B(_1i9(_1ic.b,_1ie-1|0));}));}};return new F(function(){return _1i9(_1hU,_1hS);});}}else{return E(_1hK);}}};if(_1hy<=_1hO){if(_1hO<=_1hy){var _1if=E(_1gH);if(_1hx<=_1if){if(_1if<=_1hx){var _1ig=E(_1er);}else{var _1ih=E(_1hx);if(!_1ih){var _1ii=B(_1hQ( -1, -1));}else{var _1ii=B(_1hQ(_1hy,_1ih-1|0));}var _1ig=_1ii;}var _1ij=_1ig;}else{if(_1hx!=(B(_7a(_1hK,0))-1|0)){var _1ik=B(_1hQ(_1hy,_1hx+1|0));}else{var _1ik=B(_1hQ( -1, -1));}var _1ij=_1ik;}var _1il=_1ij;}else{var _1im=E(_1hy);if(!_1im){var _1in=B(_1hQ( -1, -1));}else{var _1in=B(_1hQ(_1im-1|0,_1hx));}var _1il=_1in;}var _1io=_1il;}else{if(_1hy!=(B(_7a(_1hP,0))-1|0)){var _1ip=B(_1hQ(_1hy+1|0,_1hx));}else{var _1ip=B(_1hQ( -1, -1));}var _1io=_1ip;}var _1hN=_1io;}if(!E(_1h9)){var _1iq=E(_1hN);}else{var _1ir=new T(function(){var _1is=E(_1hN);if(!_1is._){return E(_dJ);}else{return B(_7a(_1is.a,0));}}),_1it=new T(function(){return B(_7a(_1hN,0));}),_1iu=function(_1iv,_1iw,_1ix,_1iy,_1iz,_1iA,_1iB){while(1){var _1iC=B((function(_1iD,_1iE,_1iF,_1iG,_1iH,_1iI,_1iJ){var _1iK=E(_1iJ);if(!_1iK._){return E(_1iG);}else{var _1iL=_1iK.b,_1iM=E(_1iK.a);if(!_1iM._){return E(_1eq);}else{var _1iN=_1iM.b,_1iO=E(_1iM.a);if(E(_1iO.b)==5){var _1iP=new T(function(){var _1iQ=B(_19H(_1ga,_1iD));return new T2(0,_1iQ.a,_1iQ.b);}),_1iR=new T(function(){var _1iS=function(_1iT,_1iU){var _1iV=function(_1iW){return new F(function(){return _ny(_1iE,_1iF,_1e9,_CD,new T(function(){return B(_ny(_1iT,E(_1iU),_1iO.a,_161,_1iG));}));});};if(_1iT!=_1iE){return new F(function(){return _1iV(_);});}else{if(E(_1iU)!=_1iF){return new F(function(){return _1iV(_);});}else{return E(_1iG);}}};switch(E(E(_1iP).a)){case 1:var _1iX=_1iE-1|0;if(_1iX<0){return B(_1iS(_1iE,_1iF));}else{if(_1iX>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{if(_1iF<0){return B(_1iS(_1iE,_1iF));}else{if(_1iF>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iX!=_1iH){if(E(B(_77(B(_77(_1iG,_1iF)),_1iX)).a)==32){return B(_1iS(_1iX,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1iF!=_1iI){if(E(B(_77(B(_77(_1iG,_1iF)),_1iX)).a)==32){return B(_1iS(_1iX,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;case 2:if(_1iE<0){return B(_1iS(_1iE,_1iF));}else{if(_1iE>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{var _1iY=_1iF-1|0;if(_1iY<0){return B(_1iS(_1iE,_1iF));}else{if(_1iY>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iE!=_1iH){if(E(B(_77(B(_77(_1iG,_1iY)),_1iE)).a)==32){return B(_1iS(_1iE,_1iY));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1iY!=_1iI){if(E(B(_77(B(_77(_1iG,_1iY)),_1iE)).a)==32){return B(_1iS(_1iE,_1iY));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;case 3:var _1iZ=_1iE+1|0;if(_1iZ<0){return B(_1iS(_1iE,_1iF));}else{if(_1iZ>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{if(_1iF<0){return B(_1iS(_1iE,_1iF));}else{if(_1iF>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iZ!=_1iH){if(E(B(_77(B(_77(_1iG,_1iF)),_1iZ)).a)==32){return B(_1iS(_1iZ,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1iF!=_1iI){if(E(B(_77(B(_77(_1iG,_1iF)),_1iZ)).a)==32){return B(_1iS(_1iZ,_1iF));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;case 4:if(_1iE<0){return B(_1iS(_1iE,_1iF));}else{if(_1iE>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{var _1j0=_1iF+1|0;if(_1j0<0){return B(_1iS(_1iE,_1iF));}else{if(_1j0>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iE!=_1iH){if(E(B(_77(B(_77(_1iG,_1j0)),_1iE)).a)==32){return B(_1iS(_1iE,_1j0));}else{return B(_1iS(_1iE,_1iF));}}else{if(_1j0!=_1iI){if(E(B(_77(B(_77(_1iG,_1j0)),_1iE)).a)==32){return B(_1iS(_1iE,_1j0));}else{return B(_1iS(_1iE,_1iF));}}else{return B(_1iS(_1iE,_1iF));}}}}}}break;default:if(_1iE<0){return B(_1iS(_1iE,_1iF));}else{if(_1iE>=E(_1ir)){return B(_1iS(_1iE,_1iF));}else{if(_1iF<0){return B(_1iS(_1iE,_1iF));}else{if(_1iF>=E(_1it)){return B(_1iS(_1iE,_1iF));}else{if(_1iE!=_1iH){var _1j1=E(B(_77(B(_77(_1iG,_1iF)),_1iE)).a);return B(_1iS(_1iE,_1iF));}else{if(_1iF!=_1iI){var _1j2=E(B(_77(B(_77(_1iG,_1iF)),_1iE)).a);return B(_1iS(_1iE,_1iF));}else{return B(_1iS(_1iE,_1iF));}}}}}}}}),_1j3=E(_1iN);if(!_1j3._){var _1j4=_1iF+1|0,_1j5=_1iH,_1j6=_1iI;_1iv=new T(function(){return E(E(_1iP).b);},1);_1iw=0;_1ix=_1j4;_1iy=_1iR;_1iz=_1j5;_1iA=_1j6;_1iB=_1iL;return __continue;}else{var _1j7=_1iE+1|0,_1j4=_1iF,_1j5=_1iH,_1j6=_1iI;_1iv=new T(function(){return E(E(_1iP).b);},1);_1iw=_1j7;_1ix=_1j4;_1iy=_1iR;_1iz=_1j5;_1iA=_1j6;_1iB=new T2(1,_1j3,_1iL);return __continue;}}else{var _1j8=E(_1iN);if(!_1j8._){var _1j9=_1iD,_1j4=_1iF+1|0,_1ja=_1iG,_1j5=_1iH,_1j6=_1iI;_1iv=_1j9;_1iw=0;_1ix=_1j4;_1iy=_1ja;_1iz=_1j5;_1iA=_1j6;_1iB=_1iL;return __continue;}else{var _1j9=_1iD,_1j7=_1iE+1|0,_1j4=_1iF,_1ja=_1iG,_1j5=_1iH,_1j6=_1iI;_1iv=_1j9;_1iw=_1j7;_1ix=_1j4;_1iy=_1ja;_1iz=_1j5;_1iA=_1j6;_1iB=new T2(1,_1j8,_1iL);return __continue;}}}}})(_1iv,_1iw,_1ix,_1iy,_1iz,_1iA,_1iB));if(_1iC!=__continue){return _1iC;}}},_1iq=B(_1iu(_1gZ,0,0,_1hN,_1hy,_1hx,_1hN));}var _1jb=function(_1jc){var _1jd=function(_1je){var _1jf=new T(function(){switch(E(_1hB)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1jg=new T(function(){if(!E(_1hL)){if(!E(_1jf)){return new T2(0,_1hy,_1hx);}else{return E(_1hf);}}else{if(!B(_6g(_6U,_1iq,_1hK))){if(!E(_1jf)){return new T2(0,_1hy,_1hx);}else{return E(_1hf);}}else{return E(_1hf);}}}),_1jh=new T(function(){return E(E(_1jg).b);}),_1ji=new T(function(){return E(E(_1jg).a);});if(!E(_1hL)){var _1jj=E(_1h2);}else{var _1jj=E(B(_V2(new T(function(){return B(_1bC(_1gN,_1dU,_1iq));}),_1iq)).a);}var _1jk=new T(function(){if(!E(_1hJ)){if(!E(_1hE)){var _1jl=function(_1jm){var _1jn=function(_1jo){var _1jp=E(_1hB);if(_1jp==4){return new T2(1,_1en,new T2(1,_1hA,_10));}else{if(!E(_1jf)){return (E(_1jp)==2)?new T2(1,_1ep,new T2(1,_1hA,_10)):__Z;}else{var _1jq=E(_1hA);return (E(_1jq)==61)?new T2(1,_1eo,new T2(1,_1jq,new T(function(){return B(_I(0,_1hx,_10));}))):new T2(1,_1eo,new T2(1,_1jq,_10));}}};if(!E(_1hL)){return new F(function(){return _1jn(_);});}else{if(E(_1gG)!=E(_1ji)){return new T2(1,_1em,new T2(1,_1hA,_10));}else{if(E(_1gH)!=E(_1jh)){return new T2(1,_1em,new T2(1,_1hA,_10));}else{return new F(function(){return _1jn(_);});}}}};if(!E(_1hL)){return B(_1jl(_));}else{if(!E(_1jj)){return B(_1jl(_));}else{return E(_1ef);}}}else{return new T2(1,_1ej,new T2(1,_1hA,_10));}}else{return new T2(1,_1ei,new T2(1,_1hA,_10));}},1);return {_:0,a:E(new T2(0,_1ji,_1jh)),b:E(_1he),c:E(_1iq),d:_1jc,e:_1je,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(B(_y(_1gQ,_1jk))),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1jj),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_sd),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_1ha),C:E(_1hb),D:_1hc};};if(!E(_1hJ)){return new F(function(){return _1jd(_1gM);});}else{return new F(function(){return _1jd(E(_1hA));});}};if(!E(_1hE)){return new F(function(){return _1jb(_1gL);});}else{return new F(function(){return _1jb(E(_1hA));});}},_1jr=function(_1js,_1jt){var _1ju=E(_1jt),_1jv=B(_77(B(_77(_1gK,_1ju)),_1js)),_1jw=_1jv.a,_1jx=_1jv.b;if(E(_1gM)==32){if(!B(_4B(_6f,_1jw,_1a9))){var _1jy=false;}else{switch(E(_1jx)){case 0:var _1jz=true;break;case 1:var _1jz=false;break;case 2:var _1jz=false;break;case 3:var _1jz=false;break;case 4:var _1jz=false;break;case 5:var _1jz=false;break;case 6:var _1jz=false;break;case 7:var _1jz=false;break;default:var _1jz=false;}var _1jy=_1jz;}var _1jA=_1jy;}else{var _1jA=false;}if(E(_1gM)==32){if(E(_1jw)==32){var _1jB=false;}else{switch(E(_1jx)){case 0:if(!E(_1jA)){var _1jC=true;}else{var _1jC=false;}var _1jD=_1jC;break;case 1:var _1jD=false;break;case 2:var _1jD=false;break;case 3:var _1jD=false;break;case 4:var _1jD=false;break;case 5:var _1jD=false;break;case 6:var _1jD=false;break;case 7:var _1jD=false;break;default:if(!E(_1jA)){var _1jE=true;}else{var _1jE=false;}var _1jD=_1jE;}var _1jB=_1jD;}var _1jF=_1jB;}else{var _1jF=false;}var _1jG=new T(function(){return B(_ny(_1js,_1ju,new T(function(){if(!E(_1jF)){if(!E(_1jA)){return E(_1jw);}else{return _1gL;}}else{return E(_1e9);}}),_1jx,_1gK));});switch(E(_1jx)){case 3:var _1jH=true;break;case 4:if(E(_1gM)==32){var _1jI=true;}else{var _1jI=false;}var _1jH=_1jI;break;default:var _1jH=false;}if(!E(_1jH)){var _1jJ=E(_1jG);}else{var _1jK=E(_1gG),_1jL=new T(function(){return B(_77(_1jG,_1ju));}),_1jM=function(_1jN,_1jO){var _1jP=E(_1jN);if(_1jP==( -1)){return E(_1jG);}else{var _1jQ=new T(function(){return B(_ny(_1js,_1ju,_1e9,_CD,_1jG));}),_1jR=E(_1jO);if(_1jR==( -1)){var _1jS=__Z;}else{var _1jS=B(_77(_1jQ,_1jR));}if(E(B(_77(_1jS,_1jP)).a)==32){var _1jT=new T(function(){var _1jU=new T(function(){return B(_77(_1jL,_1js));}),_1jV=new T2(1,new T2(0,new T(function(){return E(E(_1jU).a);}),new T(function(){return E(E(_1jU).b);})),new T(function(){var _1jW=_1jP+1|0;if(_1jW>0){return B(_19V(_1jW,_1jS));}else{return E(_1jS);}}));if(0>=_1jP){return E(_1jV);}else{var _1jX=function(_1jY,_1jZ){var _1k0=E(_1jY);if(!_1k0._){return E(_1jV);}else{var _1k1=_1k0.a,_1k2=E(_1jZ);return (_1k2==1)?new T2(1,_1k1,_1jV):new T2(1,_1k1,new T(function(){return B(_1jX(_1k0.b,_1k2-1|0));}));}};return B(_1jX(_1jS,_1jP));}}),_1k3=new T2(1,_1jT,new T(function(){var _1k4=_1jO+1|0;if(_1k4>0){return B(_1a1(_1k4,_1jQ));}else{return E(_1jQ);}}));if(0>=_1jO){return E(_1k3);}else{var _1k5=function(_1k6,_1k7){var _1k8=E(_1k6);if(!_1k8._){return E(_1k3);}else{var _1k9=_1k8.a,_1ka=E(_1k7);return (_1ka==1)?new T2(1,_1k9,_1k3):new T2(1,_1k9,new T(function(){return B(_1k5(_1k8.b,_1ka-1|0));}));}};return new F(function(){return _1k5(_1jQ,_1jO);});}}else{return E(_1jG);}}};if(_1js<=_1jK){if(_1jK<=_1js){var _1kb=E(_1gH);if(_1ju<=_1kb){if(_1kb<=_1ju){var _1kc=E(_1er);}else{var _1kd=E(_1ju);if(!_1kd){var _1ke=B(_1jM( -1, -1));}else{var _1ke=B(_1jM(_1js,_1kd-1|0));}var _1kc=_1ke;}var _1kf=_1kc;}else{if(_1ju!=(B(_7a(_1jG,0))-1|0)){var _1kg=B(_1jM(_1js,_1ju+1|0));}else{var _1kg=B(_1jM( -1, -1));}var _1kf=_1kg;}var _1kh=_1kf;}else{var _1ki=E(_1js);if(!_1ki){var _1kj=B(_1jM( -1, -1));}else{var _1kj=B(_1jM(_1ki-1|0,_1ju));}var _1kh=_1kj;}var _1kk=_1kh;}else{if(_1js!=(B(_7a(_1jL,0))-1|0)){var _1kl=B(_1jM(_1js+1|0,_1ju));}else{var _1kl=B(_1jM( -1, -1));}var _1kk=_1kl;}var _1jJ=_1kk;}if(!E(_1h9)){var _1km=E(_1jJ);}else{var _1kn=new T(function(){var _1ko=E(_1jJ);if(!_1ko._){return E(_dJ);}else{return B(_7a(_1ko.a,0));}}),_1kp=new T(function(){return B(_7a(_1jJ,0));}),_1kq=function(_1kr,_1ks,_1kt,_1ku,_1kv,_1kw,_1kx){while(1){var _1ky=B((function(_1kz,_1kA,_1kB,_1kC,_1kD,_1kE,_1kF){var _1kG=E(_1kF);if(!_1kG._){return E(_1kC);}else{var _1kH=_1kG.b,_1kI=E(_1kG.a);if(!_1kI._){return E(_1eq);}else{var _1kJ=_1kI.b,_1kK=E(_1kI.a);if(E(_1kK.b)==5){var _1kL=new T(function(){var _1kM=B(_19H(_1ga,_1kz));return new T2(0,_1kM.a,_1kM.b);}),_1kN=new T(function(){var _1kO=function(_1kP,_1kQ){var _1kR=function(_1kS){return new F(function(){return _ny(_1kA,_1kB,_1e9,_CD,new T(function(){return B(_ny(_1kP,E(_1kQ),_1kK.a,_161,_1kC));}));});};if(_1kP!=_1kA){return new F(function(){return _1kR(_);});}else{if(E(_1kQ)!=_1kB){return new F(function(){return _1kR(_);});}else{return E(_1kC);}}};switch(E(E(_1kL).a)){case 1:var _1kT=_1kA-1|0;if(_1kT<0){return B(_1kO(_1kA,_1kB));}else{if(_1kT>=E(_1kn)){return B(_1kO(_1kA,_1kB));}else{if(_1kB<0){return B(_1kO(_1kA,_1kB));}else{if(_1kB>=E(_1kp)){return B(_1kO(_1kA,_1kB));}else{if(_1kT!=_1kD){if(E(B(_77(B(_77(_1kC,_1kB)),_1kT)).a)==32){return B(_1kO(_1kT,_1kB));}else{return B(_1kO(_1kA,_1kB));}}else{if(_1kB!=_1kE){if(E(B(_77(B(_77(_1kC,_1kB)),_1kT)).a)==32){return B(_1kO(_1kT,_1kB));}else{return B(_1kO(_1kA,_1kB));}}else{return B(_1kO(_1kA,_1kB));}}}}}}break;case 2:if(_1kA<0){return B(_1kO(_1kA,_1kB));}else{if(_1kA>=E(_1kn)){return B(_1kO(_1kA,_1kB));}else{var _1kU=_1kB-1|0;if(_1kU<0){return B(_1kO(_1kA,_1kB));}else{if(_1kU>=E(_1kp)){return B(_1kO(_1kA,_1kB));}else{if(_1kA!=_1kD){if(E(B(_77(B(_77(_1kC,_1kU)),_1kA)).a)==32){return B(_1kO(_1kA,_1kU));}else{return B(_1kO(_1kA,_1kB));}}else{if(_1kU!=_1kE){if(E(B(_77(B(_77(_1kC,_1kU)),_1kA)).a)==32){return B(_1kO(_1kA,_1kU));}else{return B(_1kO(_1kA,_1kB));}}else{return B(_1kO(_1kA,_1kB));}}}}}}break;case 3:var _1kV=_1kA+1|0;if(_1kV<0){return B(_1kO(_1kA,_1kB));}else{if(_1kV>=E(_1kn)){return B(_1kO(_1kA,_1kB));}else{if(_1kB<0){return B(_1kO(_1kA,_1kB));}else{if(_1kB>=E(_1kp)){return B(_1kO(_1kA,_1kB));}else{if(_1kV!=_1kD){if(E(B(_77(B(_77(_1kC,_1kB)),_1kV)).a)==32){return B(_1kO(_1kV,_1kB));}else{return B(_1kO(_1kA,_1kB));}}else{if(_1kB!=_1kE){if(E(B(_77(B(_77(_1kC,_1kB)),_1kV)).a)==32){return B(_1kO(_1kV,_1kB));}else{return B(_1kO(_1kA,_1kB));}}else{return B(_1kO(_1kA,_1kB));}}}}}}break;case 4:if(_1kA<0){return B(_1kO(_1kA,_1kB));}else{if(_1kA>=E(_1kn)){return B(_1kO(_1kA,_1kB));}else{var _1kW=_1kB+1|0;if(_1kW<0){return B(_1kO(_1kA,_1kB));}else{if(_1kW>=E(_1kp)){return B(_1kO(_1kA,_1kB));}else{if(_1kA!=_1kD){if(E(B(_77(B(_77(_1kC,_1kW)),_1kA)).a)==32){return B(_1kO(_1kA,_1kW));}else{return B(_1kO(_1kA,_1kB));}}else{if(_1kW!=_1kE){if(E(B(_77(B(_77(_1kC,_1kW)),_1kA)).a)==32){return B(_1kO(_1kA,_1kW));}else{return B(_1kO(_1kA,_1kB));}}else{return B(_1kO(_1kA,_1kB));}}}}}}break;default:if(_1kA<0){return B(_1kO(_1kA,_1kB));}else{if(_1kA>=E(_1kn)){return B(_1kO(_1kA,_1kB));}else{if(_1kB<0){return B(_1kO(_1kA,_1kB));}else{if(_1kB>=E(_1kp)){return B(_1kO(_1kA,_1kB));}else{if(_1kA!=_1kD){var _1kX=E(B(_77(B(_77(_1kC,_1kB)),_1kA)).a);return B(_1kO(_1kA,_1kB));}else{if(_1kB!=_1kE){var _1kY=E(B(_77(B(_77(_1kC,_1kB)),_1kA)).a);return B(_1kO(_1kA,_1kB));}else{return B(_1kO(_1kA,_1kB));}}}}}}}}),_1kZ=E(_1kJ);if(!_1kZ._){var _1l0=_1kB+1|0,_1l1=_1kD,_1l2=_1kE;_1kr=new T(function(){return E(E(_1kL).b);},1);_1ks=0;_1kt=_1l0;_1ku=_1kN;_1kv=_1l1;_1kw=_1l2;_1kx=_1kH;return __continue;}else{var _1l3=_1kA+1|0,_1l0=_1kB,_1l1=_1kD,_1l2=_1kE;_1kr=new T(function(){return E(E(_1kL).b);},1);_1ks=_1l3;_1kt=_1l0;_1ku=_1kN;_1kv=_1l1;_1kw=_1l2;_1kx=new T2(1,_1kZ,_1kH);return __continue;}}else{var _1l4=E(_1kJ);if(!_1l4._){var _1l5=_1kz,_1l0=_1kB+1|0,_1l6=_1kC,_1l1=_1kD,_1l2=_1kE;_1kr=_1l5;_1ks=0;_1kt=_1l0;_1ku=_1l6;_1kv=_1l1;_1kw=_1l2;_1kx=_1kH;return __continue;}else{var _1l5=_1kz,_1l3=_1kA+1|0,_1l0=_1kB,_1l6=_1kC,_1l1=_1kD,_1l2=_1kE;_1kr=_1l5;_1ks=_1l3;_1kt=_1l0;_1ku=_1l6;_1kv=_1l1;_1kw=_1l2;_1kx=new T2(1,_1l4,_1kH);return __continue;}}}}})(_1kr,_1ks,_1kt,_1ku,_1kv,_1kw,_1kx));if(_1ky!=__continue){return _1ky;}}},_1km=B(_1kq(_1gZ,0,0,_1jJ,_1js,_1ju,_1jJ));}var _1l7=function(_1l8){var _1l9=function(_1la){var _1lb=new T(function(){switch(E(_1jx)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1lc=new T(function(){if(!E(_1jH)){if(!E(_1lb)){return new T2(0,_1js,_1ju);}else{return E(_1hf);}}else{if(!B(_6g(_6U,_1km,_1jG))){if(!E(_1lb)){return new T2(0,_1js,_1ju);}else{return E(_1hf);}}else{return E(_1hf);}}}),_1ld=new T(function(){return E(E(_1lc).b);}),_1le=new T(function(){return E(E(_1lc).a);});if(!E(_1jH)){var _1lf=E(_1h2);}else{var _1lf=E(B(_V2(new T(function(){return B(_1bC(_1gN,_1dU,_1km));}),_1km)).a);}var _1lg=new T(function(){if(!E(_1jF)){if(!E(_1jA)){var _1lh=function(_1li){var _1lj=function(_1lk){var _1ll=E(_1jx);if(_1ll==4){return new T2(1,_1en,new T2(1,_1jw,_10));}else{if(!E(_1lb)){return (E(_1ll)==2)?new T2(1,_1ep,new T2(1,_1jw,_10)):__Z;}else{var _1lm=E(_1jw);return (E(_1lm)==61)?new T2(1,_1eo,new T2(1,_1lm,new T(function(){return B(_I(0,_1ju,_10));}))):new T2(1,_1eo,new T2(1,_1lm,_10));}}};if(!E(_1jH)){return new F(function(){return _1lj(_);});}else{if(E(_1gG)!=E(_1le)){return new T2(1,_1em,new T2(1,_1jw,_10));}else{if(E(_1gH)!=E(_1ld)){return new T2(1,_1em,new T2(1,_1jw,_10));}else{return new F(function(){return _1lj(_);});}}}};if(!E(_1jH)){return B(_1lh(_));}else{if(!E(_1lf)){return B(_1lh(_));}else{return E(_1ef);}}}else{return new T2(1,_1ej,new T2(1,_1jw,_10));}}else{return new T2(1,_1ei,new T2(1,_1jw,_10));}},1);return {_:0,a:E(new T2(0,_1le,_1ld)),b:E(_1he),c:E(_1km),d:_1l8,e:_1la,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(B(_y(_1gQ,_1lg))),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1lf),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_sd),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_1ha),C:E(_1hb),D:_1hc};};if(!E(_1jF)){return new F(function(){return _1l9(_1gM);});}else{return new F(function(){return _1l9(E(_1jw));});}};if(!E(_1jA)){return new F(function(){return _1l7(_1gL);});}else{return new F(function(){return _1l7(E(_1jw));});}};switch(E(_1ht)){case 72:var _1ln=E(_1gH);if(0<=(_1ln-1|0)){return B(_1hv(_1gG,_1ln-1|0));}else{return B(_1hv(_1gG,_1ln));}break;case 75:var _1lo=E(_1gG);if(0<=(_1lo-1|0)){return B(_1jr(_1lo-1|0,_1gH));}else{return B(_1jr(_1lo,_1gH));}break;case 77:var _1lp=E(_1gG);if(E(_1gI)!=(_1lp+1|0)){return B(_1jr(_1lp+1|0,_1gH));}else{return B(_1jr(_1lp,_1gH));}break;case 80:var _1lq=E(_1gH);if(E(_1gJ)!=(_1lq+1|0)){return B(_1hv(_1gG,_1lq+1|0));}else{return B(_1hv(_1gG,_1lq));}break;case 104:var _1lr=E(_1gG);if(0<=(_1lr-1|0)){return B(_1jr(_1lr-1|0,_1gH));}else{return B(_1jr(_1lr,_1gH));}break;case 106:var _1ls=E(_1gH);if(E(_1gJ)!=(_1ls+1|0)){return B(_1hv(_1gG,_1ls+1|0));}else{return B(_1hv(_1gG,_1ls));}break;case 107:var _1lt=E(_1gH);if(0<=(_1lt-1|0)){return B(_1hv(_1gG,_1lt-1|0));}else{return B(_1hv(_1gG,_1lt));}break;case 108:var _1lu=E(_1gG);if(E(_1gI)!=(_1lu+1|0)){return B(_1jr(_1lu+1|0,_1gH));}else{return B(_1jr(_1lu,_1gH));}break;default:var _1lv=E(_1gG),_1lw=E(_1gH),_1lx=B(_77(B(_77(_1gK,_1lw)),_1lv)),_1ly=_1lx.a,_1lz=_1lx.b;if(E(_1gM)==32){if(!B(_4B(_6f,_1ly,_1a9))){var _1lA=false;}else{switch(E(_1lz)){case 0:var _1lB=true;break;case 1:var _1lB=false;break;case 2:var _1lB=false;break;case 3:var _1lB=false;break;case 4:var _1lB=false;break;case 5:var _1lB=false;break;case 6:var _1lB=false;break;case 7:var _1lB=false;break;default:var _1lB=false;}var _1lA=_1lB;}var _1lC=_1lA;}else{var _1lC=false;}if(E(_1gM)==32){if(E(_1ly)==32){var _1lD=false;}else{switch(E(_1lz)){case 0:if(!E(_1lC)){var _1lE=true;}else{var _1lE=false;}var _1lF=_1lE;break;case 1:var _1lF=false;break;case 2:var _1lF=false;break;case 3:var _1lF=false;break;case 4:var _1lF=false;break;case 5:var _1lF=false;break;case 6:var _1lF=false;break;case 7:var _1lF=false;break;default:if(!E(_1lC)){var _1lG=true;}else{var _1lG=false;}var _1lF=_1lG;}var _1lD=_1lF;}var _1lH=_1lD;}else{var _1lH=false;}var _1lI=new T(function(){return B(_ny(_1lv,_1lw,new T(function(){if(!E(_1lH)){if(!E(_1lC)){return E(_1ly);}else{return _1gL;}}else{return E(_1e9);}}),_1lz,_1gK));});switch(E(_1lz)){case 3:var _1lJ=true;break;case 4:if(E(_1gM)==32){var _1lK=true;}else{var _1lK=false;}var _1lJ=_1lK;break;default:var _1lJ=false;}if(!E(_1lJ)){var _1lL=E(_1lI);}else{var _1lL=E(_1er);}if(!E(_1h9)){var _1lM=E(_1lL);}else{var _1lN=new T(function(){var _1lO=E(_1lL);if(!_1lO._){return E(_dJ);}else{return B(_7a(_1lO.a,0));}}),_1lP=new T(function(){return B(_7a(_1lL,0));}),_1lQ=function(_1lR,_1lS,_1lT,_1lU,_1lV,_1lW,_1lX){while(1){var _1lY=B((function(_1lZ,_1m0,_1m1,_1m2,_1m3,_1m4,_1m5){var _1m6=E(_1m5);if(!_1m6._){return E(_1m2);}else{var _1m7=_1m6.b,_1m8=E(_1m6.a);if(!_1m8._){return E(_1eq);}else{var _1m9=_1m8.b,_1ma=E(_1m8.a);if(E(_1ma.b)==5){var _1mb=new T(function(){var _1mc=B(_19H(_1ga,_1lZ));return new T2(0,_1mc.a,_1mc.b);}),_1md=new T(function(){var _1me=function(_1mf,_1mg){var _1mh=function(_1mi){return new F(function(){return _ny(_1m0,_1m1,_1e9,_CD,new T(function(){return B(_ny(_1mf,_1mg,_1ma.a,_161,_1m2));}));});};if(_1mf!=_1m0){return new F(function(){return _1mh(_);});}else{if(_1mg!=_1m1){return new F(function(){return _1mh(_);});}else{return E(_1m2);}}};switch(E(E(_1mb).a)){case 1:var _1mj=_1m0-1|0;if(_1mj<0){return B(_1me(_1m0,_1m1));}else{if(_1mj>=E(_1lN)){return B(_1me(_1m0,_1m1));}else{if(_1m1<0){return B(_1me(_1m0,_1m1));}else{if(_1m1>=E(_1lP)){return B(_1me(_1m0,_1m1));}else{if(_1mj!=_1m3){if(E(B(_77(B(_77(_1m2,_1m1)),_1mj)).a)==32){return B(_1me(_1mj,_1m1));}else{return B(_1me(_1m0,_1m1));}}else{if(_1m1!=_1m4){if(E(B(_77(B(_77(_1m2,_1m1)),_1mj)).a)==32){return B(_1me(_1mj,_1m1));}else{return B(_1me(_1m0,_1m1));}}else{return B(_1me(_1m0,_1m1));}}}}}}break;case 2:if(_1m0<0){return B(_1me(_1m0,_1m1));}else{if(_1m0>=E(_1lN)){return B(_1me(_1m0,_1m1));}else{var _1mk=_1m1-1|0;if(_1mk<0){return B(_1me(_1m0,_1m1));}else{if(_1mk>=E(_1lP)){return B(_1me(_1m0,_1m1));}else{if(_1m0!=_1m3){if(E(B(_77(B(_77(_1m2,_1mk)),_1m0)).a)==32){return B(_1me(_1m0,_1mk));}else{return B(_1me(_1m0,_1m1));}}else{if(_1mk!=_1m4){if(E(B(_77(B(_77(_1m2,_1mk)),_1m0)).a)==32){return B(_1me(_1m0,_1mk));}else{return B(_1me(_1m0,_1m1));}}else{return B(_1me(_1m0,_1m1));}}}}}}break;case 3:var _1ml=_1m0+1|0;if(_1ml<0){return B(_1me(_1m0,_1m1));}else{if(_1ml>=E(_1lN)){return B(_1me(_1m0,_1m1));}else{if(_1m1<0){return B(_1me(_1m0,_1m1));}else{if(_1m1>=E(_1lP)){return B(_1me(_1m0,_1m1));}else{if(_1ml!=_1m3){if(E(B(_77(B(_77(_1m2,_1m1)),_1ml)).a)==32){return B(_1me(_1ml,_1m1));}else{return B(_1me(_1m0,_1m1));}}else{if(_1m1!=_1m4){if(E(B(_77(B(_77(_1m2,_1m1)),_1ml)).a)==32){return B(_1me(_1ml,_1m1));}else{return B(_1me(_1m0,_1m1));}}else{return B(_1me(_1m0,_1m1));}}}}}}break;case 4:if(_1m0<0){return B(_1me(_1m0,_1m1));}else{if(_1m0>=E(_1lN)){return B(_1me(_1m0,_1m1));}else{var _1mm=_1m1+1|0;if(_1mm<0){return B(_1me(_1m0,_1m1));}else{if(_1mm>=E(_1lP)){return B(_1me(_1m0,_1m1));}else{if(_1m0!=_1m3){if(E(B(_77(B(_77(_1m2,_1mm)),_1m0)).a)==32){return B(_1me(_1m0,_1mm));}else{return B(_1me(_1m0,_1m1));}}else{if(_1mm!=_1m4){if(E(B(_77(B(_77(_1m2,_1mm)),_1m0)).a)==32){return B(_1me(_1m0,_1mm));}else{return B(_1me(_1m0,_1m1));}}else{return B(_1me(_1m0,_1m1));}}}}}}break;default:if(_1m0<0){return B(_1me(_1m0,_1m1));}else{if(_1m0>=E(_1lN)){return B(_1me(_1m0,_1m1));}else{if(_1m1<0){return B(_1me(_1m0,_1m1));}else{if(_1m1>=E(_1lP)){return B(_1me(_1m0,_1m1));}else{if(_1m0!=_1m3){var _1mn=E(B(_77(B(_77(_1m2,_1m1)),_1m0)).a);return B(_1me(_1m0,_1m1));}else{if(_1m1!=_1m4){var _1mo=E(B(_77(B(_77(_1m2,_1m1)),_1m0)).a);return B(_1me(_1m0,_1m1));}else{return B(_1me(_1m0,_1m1));}}}}}}}}),_1mp=E(_1m9);if(!_1mp._){var _1mq=_1m1+1|0,_1mr=_1m3,_1ms=_1m4;_1lR=new T(function(){return E(E(_1mb).b);},1);_1lS=0;_1lT=_1mq;_1lU=_1md;_1lV=_1mr;_1lW=_1ms;_1lX=_1m7;return __continue;}else{return new F(function(){return _1mt(new T(function(){return E(E(_1mb).b);},1),_1m0+1|0,_1m1,_1md,_1m3,_1m4,_1mp.a,_1mp.b,_1m7);});}}else{var _1mu=E(_1m9);if(!_1mu._){var _1mv=_1lZ,_1mq=_1m1+1|0,_1mw=_1m2,_1mr=_1m3,_1ms=_1m4;_1lR=_1mv;_1lS=0;_1lT=_1mq;_1lU=_1mw;_1lV=_1mr;_1lW=_1ms;_1lX=_1m7;return __continue;}else{return new F(function(){return _1mt(_1lZ,_1m0+1|0,_1m1,_1m2,_1m3,_1m4,_1mu.a,_1mu.b,_1m7);});}}}}})(_1lR,_1lS,_1lT,_1lU,_1lV,_1lW,_1lX));if(_1lY!=__continue){return _1lY;}}},_1mt=function(_1mx,_1my,_1mz,_1mA,_1mB,_1mC,_1mD,_1mE,_1mF){while(1){var _1mG=B((function(_1mH,_1mI,_1mJ,_1mK,_1mL,_1mM,_1mN,_1mO,_1mP){var _1mQ=E(_1mN);if(E(_1mQ.b)==5){var _1mR=new T(function(){var _1mS=B(_19H(_1ga,_1mH));return new T2(0,_1mS.a,_1mS.b);}),_1mT=new T(function(){var _1mU=function(_1mV,_1mW){var _1mX=function(_1mY){return new F(function(){return _ny(_1mI,_1mJ,_1e9,_CD,new T(function(){return B(_ny(_1mV,_1mW,_1mQ.a,_161,_1mK));}));});};if(_1mV!=_1mI){return new F(function(){return _1mX(_);});}else{if(_1mW!=_1mJ){return new F(function(){return _1mX(_);});}else{return E(_1mK);}}};switch(E(E(_1mR).a)){case 1:var _1mZ=_1mI-1|0;if(_1mZ<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mZ>=E(_1lN)){return B(_1mU(_1mI,_1mJ));}else{if(_1mJ<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mJ>=E(_1lP)){return B(_1mU(_1mI,_1mJ));}else{if(_1mZ!=_1mL){if(E(B(_77(B(_77(_1mK,_1mJ)),_1mZ)).a)==32){return B(_1mU(_1mZ,_1mJ));}else{return B(_1mU(_1mI,_1mJ));}}else{if(_1mJ!=_1mM){if(E(B(_77(B(_77(_1mK,_1mJ)),_1mZ)).a)==32){return B(_1mU(_1mZ,_1mJ));}else{return B(_1mU(_1mI,_1mJ));}}else{return B(_1mU(_1mI,_1mJ));}}}}}}break;case 2:if(_1mI<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mI>=E(_1lN)){return B(_1mU(_1mI,_1mJ));}else{var _1n0=_1mJ-1|0;if(_1n0<0){return B(_1mU(_1mI,_1mJ));}else{if(_1n0>=E(_1lP)){return B(_1mU(_1mI,_1mJ));}else{if(_1mI!=_1mL){if(E(B(_77(B(_77(_1mK,_1n0)),_1mI)).a)==32){return B(_1mU(_1mI,_1n0));}else{return B(_1mU(_1mI,_1mJ));}}else{if(_1n0!=_1mM){if(E(B(_77(B(_77(_1mK,_1n0)),_1mI)).a)==32){return B(_1mU(_1mI,_1n0));}else{return B(_1mU(_1mI,_1mJ));}}else{return B(_1mU(_1mI,_1mJ));}}}}}}break;case 3:var _1n1=_1mI+1|0;if(_1n1<0){return B(_1mU(_1mI,_1mJ));}else{if(_1n1>=E(_1lN)){return B(_1mU(_1mI,_1mJ));}else{if(_1mJ<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mJ>=E(_1lP)){return B(_1mU(_1mI,_1mJ));}else{if(_1n1!=_1mL){if(E(B(_77(B(_77(_1mK,_1mJ)),_1n1)).a)==32){return B(_1mU(_1n1,_1mJ));}else{return B(_1mU(_1mI,_1mJ));}}else{if(_1mJ!=_1mM){if(E(B(_77(B(_77(_1mK,_1mJ)),_1n1)).a)==32){return B(_1mU(_1n1,_1mJ));}else{return B(_1mU(_1mI,_1mJ));}}else{return B(_1mU(_1mI,_1mJ));}}}}}}break;case 4:if(_1mI<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mI>=E(_1lN)){return B(_1mU(_1mI,_1mJ));}else{var _1n2=_1mJ+1|0;if(_1n2<0){return B(_1mU(_1mI,_1mJ));}else{if(_1n2>=E(_1lP)){return B(_1mU(_1mI,_1mJ));}else{if(_1mI!=_1mL){if(E(B(_77(B(_77(_1mK,_1n2)),_1mI)).a)==32){return B(_1mU(_1mI,_1n2));}else{return B(_1mU(_1mI,_1mJ));}}else{if(_1n2!=_1mM){if(E(B(_77(B(_77(_1mK,_1n2)),_1mI)).a)==32){return B(_1mU(_1mI,_1n2));}else{return B(_1mU(_1mI,_1mJ));}}else{return B(_1mU(_1mI,_1mJ));}}}}}}break;default:if(_1mI<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mI>=E(_1lN)){return B(_1mU(_1mI,_1mJ));}else{if(_1mJ<0){return B(_1mU(_1mI,_1mJ));}else{if(_1mJ>=E(_1lP)){return B(_1mU(_1mI,_1mJ));}else{if(_1mI!=_1mL){var _1n3=E(B(_77(B(_77(_1mK,_1mJ)),_1mI)).a);return B(_1mU(_1mI,_1mJ));}else{if(_1mJ!=_1mM){var _1n4=E(B(_77(B(_77(_1mK,_1mJ)),_1mI)).a);return B(_1mU(_1mI,_1mJ));}else{return B(_1mU(_1mI,_1mJ));}}}}}}}}),_1n5=E(_1mO);if(!_1n5._){return new F(function(){return _1lQ(new T(function(){return E(E(_1mR).b);},1),0,_1mJ+1|0,_1mT,_1mL,_1mM,_1mP);});}else{var _1n6=_1mI+1|0,_1n7=_1mJ,_1n8=_1mL,_1n9=_1mM,_1na=_1mP;_1mx=new T(function(){return E(E(_1mR).b);},1);_1my=_1n6;_1mz=_1n7;_1mA=_1mT;_1mB=_1n8;_1mC=_1n9;_1mD=_1n5.a;_1mE=_1n5.b;_1mF=_1na;return __continue;}}else{var _1nb=E(_1mO);if(!_1nb._){return new F(function(){return _1lQ(_1mH,0,_1mJ+1|0,_1mK,_1mL,_1mM,_1mP);});}else{var _1nc=_1mH,_1n6=_1mI+1|0,_1n7=_1mJ,_1nd=_1mK,_1n8=_1mL,_1n9=_1mM,_1na=_1mP;_1mx=_1nc;_1my=_1n6;_1mz=_1n7;_1mA=_1nd;_1mB=_1n8;_1mC=_1n9;_1mD=_1nb.a;_1mE=_1nb.b;_1mF=_1na;return __continue;}}})(_1mx,_1my,_1mz,_1mA,_1mB,_1mC,_1mD,_1mE,_1mF));if(_1mG!=__continue){return _1mG;}}},_1lM=B(_1lQ(_1gZ,0,0,_1lL,_1lv,_1lw,_1lL));}var _1ne=function(_1nf){var _1ng=function(_1nh){var _1ni=new T(function(){switch(E(_1lz)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1nj=new T(function(){if(!E(_1lJ)){if(!E(_1ni)){return new T2(0,_1lv,_1lw);}else{return E(_1hf);}}else{if(!B(_6g(_6U,_1lM,_1lI))){if(!E(_1ni)){return new T2(0,_1lv,_1lw);}else{return E(_1hf);}}else{return E(_1hf);}}}),_1nk=new T(function(){return E(E(_1nj).b);}),_1nl=new T(function(){return E(E(_1nj).a);});if(!E(_1lJ)){var _1nm=E(_1h2);}else{var _1nm=E(B(_V2(new T(function(){return B(_1bC(_1gN,_1dU,_1lM));}),_1lM)).a);}var _1nn=new T(function(){if(!E(_1lH)){if(!E(_1lC)){var _1no=function(_1np){var _1nq=function(_1nr){var _1ns=E(_1lz);if(_1ns==4){return new T2(1,_1en,new T2(1,_1ly,_10));}else{if(!E(_1ni)){return (E(_1ns)==2)?new T2(1,_1ep,new T2(1,_1ly,_10)):__Z;}else{var _1nt=E(_1ly);return (E(_1nt)==61)?new T2(1,_1eo,new T2(1,_1nt,new T(function(){return B(_I(0,_1lw,_10));}))):new T2(1,_1eo,new T2(1,_1nt,_10));}}};if(!E(_1lJ)){return new F(function(){return _1nq(_);});}else{if(_1lv!=E(_1nl)){return new T2(1,_1em,new T2(1,_1ly,_10));}else{if(_1lw!=E(_1nk)){return new T2(1,_1em,new T2(1,_1ly,_10));}else{return new F(function(){return _1nq(_);});}}}};if(!E(_1lJ)){return B(_1no(_));}else{if(!E(_1nm)){return B(_1no(_));}else{return E(_1ef);}}}else{return new T2(1,_1ej,new T2(1,_1ly,_10));}}else{return new T2(1,_1ei,new T2(1,_1ly,_10));}},1);return {_:0,a:E(new T2(0,_1nl,_1nk)),b:E(_1he),c:E(_1lM),d:_1nf,e:_1nh,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(B(_y(_1gQ,_1nn))),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1nm),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_sd),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_1ha),C:E(_1hb),D:_1hc};};if(!E(_1lH)){return new F(function(){return _1ng(_1gM);});}else{return new F(function(){return _1ng(E(_1ly));});}};if(!E(_1lC)){return B(_1ne(_1gL));}else{return B(_1ne(E(_1ly)));}}}),_1nu=new T(function(){if(E(_1ht)==32){var _1nv=E(_1hu),_1nw=_1nv.b,_1nx=_1nv.c,_1ny=_1nv.d,_1nz=_1nv.e,_1nA=_1nv.f,_1nB=_1nv.g,_1nC=_1nv.h,_1nD=_1nv.i,_1nE=_1nv.j,_1nF=_1nv.k,_1nG=_1nv.l,_1nH=_1nv.m,_1nI=_1nv.n,_1nJ=_1nv.o,_1nK=_1nv.p,_1nL=_1nv.r,_1nM=_1nv.s,_1nN=_1nv.u,_1nO=_1nv.v,_1nP=_1nv.w,_1nQ=_1nv.x,_1nR=_1nv.y,_1nS=_1nv.z,_1nT=_1nv.A,_1nU=_1nv.B,_1nV=_1nv.C,_1nW=_1nv.D,_1nX=E(_1nv.a),_1nY=_1nX.a,_1nZ=E(_1nX.b),_1o0=new T(function(){return B(_77(B(_77(_1nx,_1nZ)),E(_1nY)));}),_1o1=new T(function(){return E(E(_1o0).b);}),_1o2=new T(function(){if(E(_1o1)==4){return true;}else{return false;}}),_1o3=new T(function(){return E(E(_1o0).a);});if(E(_1nz)==32){var _1o4=false;}else{if(E(_1o3)==32){var _1o5=true;}else{var _1o5=false;}var _1o4=_1o5;}var _1o6=new T(function(){var _1o7=new T(function(){return B(A3(_77,_1a7,B(_jf(_6f,_1ny,_1a9)),_1nz));});if(!E(_1o4)){if(!E(_1o2)){return E(_1o3);}else{if(!B(_4B(_3M,_1nA,_1aD))){return E(_1o3);}else{return B(A(_77,[_1aB,B(_jf(_3M,_1nA,_1aD)),_1o7,_1o3]));}}}else{return E(_1o7);}}),_1o8=B(_ny(_1nY,_1nZ,_1o6,_1o1,_1nx)),_1o9=B(_V2(new T(function(){return B(_1bC(_1nA,_1dU,_1o8));}),_1o8)).a;if(!E(_1o4)){var _1oa=B(_y(_1nD,new T(function(){if(!E(_1o9)){if(!E(_1o2)){return __Z;}else{return new T2(1,_1eh,new T2(1,_1o6,_10));}}else{return E(_1ef);}},1))),_1ob=B(_17x(_1dV,_1oa,_1nC,_1nX,_1nw,_1o8,_1ny,_1nz,_1nA,_1nB,_1nC,_1oa,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK,E(_1hp),_1nL,_1nM,E(_1o9),_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU,_1nV,_1nW));return {_:0,a:E(_1ob.a),b:E(_1ob.b),c:E(_1ob.c),d:_1ob.d,e:_1ob.e,f:_1ob.f,g:E(_1ob.g),h:E(_1ob.h),i:E(_1ob.i),j:E(_1ob.j),k:E(_1ob.k),l:E(_1ob.l),m:_1ob.m,n:_1ob.n,o:_1ob.o,p:_1ob.p,q:_1ob.q,r:E(_1ob.r),s:_1ob.s,t:E(_1ob.t),u:E(_1ob.u),v:E(_1ob.v),w:E(_1ob.w),x:E(_1ob.x),y:E(_1ob.y),z:E(_1ob.z),A:E(_1ob.A),B:E(_1ob.B),C:E(_1ob.C),D:_1ob.D};}else{var _1oc=B(_y(_1nD,new T(function(){if(!E(_1o9)){return new T2(1,_1eg,new T2(1,_1o6,_10));}else{return E(_1ef);}},1))),_1od=B(_17x(_1dV,_1oc,_1nC,_1nX,_1nw,_1o8,_1ny,32,_1nA,_1nB,_1nC,_1oc,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK,E(_1hp),_1nL,_1nM,E(_1o9),_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU,_1nV,_1nW));return {_:0,a:E(_1od.a),b:E(_1od.b),c:E(_1od.c),d:_1od.d,e:_1od.e,f:_1od.f,g:E(_1od.g),h:E(_1od.h),i:E(_1od.i),j:E(_1od.j),k:E(_1od.k),l:E(_1od.l),m:_1od.m,n:_1od.n,o:_1od.o,p:_1od.p,q:_1od.q,r:E(_1od.r),s:_1od.s,t:E(_1od.t),u:E(_1od.u),v:E(_1od.v),w:E(_1od.w),x:E(_1od.x),y:E(_1od.y),z:E(_1od.z),A:E(_1od.A),B:E(_1od.B),C:E(_1od.C),D:_1od.D};}}else{var _1oe=E(_1hu),_1of=_1oe.h,_1og=_1oe.i,_1oh=B(_17x(_1dV,_1og,_1of,_1oe.a,_1oe.b,_1oe.c,_1oe.d,_1oe.e,_1oe.f,_1oe.g,_1of,_1og,_1oe.j,_1oe.k,_1oe.l,_1oe.m,_1oe.n,_1oe.o,_1oe.p,E(_1hp),_1oe.r,_1oe.s,_1oe.t,_1oe.u,_1oe.v,_1oe.w,_1oe.x,_1oe.y,_1oe.z,_1oe.A,_1oe.B,_1oe.C,_1oe.D));return {_:0,a:E(_1oh.a),b:E(_1oh.b),c:E(_1oh.c),d:_1oh.d,e:_1oh.e,f:_1oh.f,g:E(_1oh.g),h:E(_1oh.h),i:E(_1oh.i),j:E(_1oh.j),k:E(_1oh.k),l:E(_1oh.l),m:_1oh.m,n:_1oh.n,o:_1oh.o,p:_1oh.p,q:_1oh.q,r:E(_1oh.r),s:_1oh.s,t:E(_1oh.t),u:E(_1oh.u),v:E(_1oh.v),w:E(_1oh.w),x:E(_1oh.x),y:E(_1oh.y),z:E(_1oh.z),A:E(_1oh.A),B:E(_1oh.B),C:E(_1oh.C),D:_1oh.D};}}),_1oi=B(_dT(_1hr,_1hs,new T(function(){return 26-E(E(E(_1nu).b).a)|0;}),_ep,new T(function(){return E(E(_1nu).c);}),_)),_1oj=E(_1nu),_1ok=_1oj.d,_1ol=_1oj.f,_1om=_1oj.g,_1on=_1oj.h,_1oo=_1oj.j,_1op=_1oj.k,_1oq=_1oj.m,_1or=_1oj.n,_1os=_1oj.o,_1ot=_1oj.p,_1ou=_1oj.q,_1ov=_1oj.r,_1ow=_1oj.s,_1ox=_1oj.u,_1oy=_1oj.x,_1oz=_1oj.y,_1oA=_1oj.z,_1oB=_1oj.B,_1oC=_1oj.C,_1oD=_1oj.D,_1oE=E(_1oj.l),_1oF=function(_){var _1oG=function(_1oH){var _1oI=function(_1oJ){if(_1oJ!=E(_1ed)){var _1oK=B(_77(_10S,_1oJ)),_1oL=B(_77(_10I,_1oJ)),_1oM=_1oL.a,_1oN=E(_1oL.b),_1oO=B(_Xh(_1oM,_1oN,new T(function(){return B(_77(_15W,_1oJ));})));return new F(function(){return _1gD(_1hq,_1ec,_1oK.a,_1oK.b,_1oM,_1oN,_1oO,B(_77(_10V,_1oJ)),32,_1oJ,_10,_1on,B(_y(_1oj.i,new T2(1,_1eb,new T(function(){return B(_I(0,_1ol,_10));})))),_1oo,_1op,_1oE.a,_1oE.b,_1oq,_1or,_1os, -1,_1ou,_1ov,_1ow,_sd,_sd,_sd,_sd,_1oy,_1oz,_1oA,B(_1ck(_1ea,_1oO)),_1oB,_1oC,_1oD,_);});}else{var _1oP=__app1(E(_dK),_1hs),_1oQ=B(A2(_dM,_1hr,_)),_1oR=B(A(_dg,[_1hr,_dL,_1g7,_1ga,_1e8,_])),_1oS=B(A(_dg,[_1hr,_dL,_1e5,_1e7,_1e6,_])),_1oT=B(A(_dg,[_1hr,_dL,_1e5,_1e4,_1e3,_])),_1oU=B(A(_dg,[_1hr,_dL,_1e2,_1e1,_1e0,_])),_1oV=B(A(_dg,[_1hr,_dL,_1ga,_1g9,_1g8,_])),_1oW=B(A(_dg,[_1hr,_dL,_1g7,_1g6,_1es,_]));return new T(function(){return {_:0,a:E(_10R),b:E(_10H),c:E(_1dW),d:E(_1ek),e:32,f:0,g:E(_1om),h:E(_1on),i:E(_10),j:E(_1oo),k:E(_1op),l:E(_1oE),m:_1oq,n:_1or,o:_1os,p:_1ot,q:_1ou,r:E(_1ov),s:_1ow,t:E(_sd),u:E(_1ox),v:E(_sd),w:E(_sd),x:E(_1oy),y:E(_1oz),z:E(_1oA),A:E(_1oj.A),B:E(_1oB),C:E(_1oC),D:_1oD};});}};if(_1ot>=0){return new F(function(){return _1oI(_1ot);});}else{return new F(function(){return _1oI(_1ol+1|0);});}};if(!E(_1ox)){if(E(_1ht)==110){return new F(function(){return _1oG(_);});}else{var _1oX=new T(function(){return E(E(_1hu).a);});if(E(_1oj.e)==32){var _1oY=B(A(_dg,[_1hr,_1dX,new T(function(){return ((E(E(_1oX).a)+1|0)+26|0)-E(_1gI)|0;},1),new T(function(){return (E(E(_1oX).b)+2|0)+1|0;},1),new T2(1,_1ok,_10),_]));return _1oj;}else{var _1oZ=B(A(_dg,[_1hr,_1ee,new T(function(){return ((E(E(_1oX).a)+1|0)+26|0)-E(_1gI)|0;},1),new T(function(){return (E(E(_1oX).b)+2|0)+1|0;},1),new T2(1,_1ok,_10),_]));return _1oj;}}}else{return new F(function(){return _1oG(_);});}};if(!E(_1oj.w)){var _1p0=new T(function(){return (2+E(_1gJ)|0)+3|0;}),_1p1=B(_Gp(_1hq,_G6,_1p0,15+_1os|0,_1p0,_1om,_));return new F(function(){return _1oF(_);});}else{return new F(function(){return _1oF(_);});}};if(!E(_1ha)){var _1p2=B(_1cO(_1gC,_1gA,_));return new F(function(){return _1hn(_);});}else{var _1p3=B(_1cO(_1gC,_1gz,_));return new F(function(){return _1hn(_);});}};if(!E(_1h2)){var _1p4=B(_1cO(_1gC,_1gA,_));return new F(function(){return _1hm(_);});}else{var _1p5=B(_1cO(_1gC,_1gz,_));return new F(function(){return _1hm(_);});}},_1p6=E(_1gS);if(!_1p6._){var _1p7=B(_1cO(_1gC,_1g4,_));return new F(function(){return _1hk(_);});}else{var _1p8=new T(function(){var _1p9=E(_1p6.a),_1pa=new T(function(){return B(A3(_1cD,_6m,new T2(1,function(_1pb){return new F(function(){return _1gc(_1p9.a,_1pb);});},new T2(1,function(_1pc){return new F(function(){return _1gc(_1p9.b,_1pc);});},_10)),new T2(1,_G,new T(function(){return B(_1gf(_1p6.b));}))));});return new T2(1,_H,_1pa);}),_1pd=B(_1cO(_1gC,new T2(1,_2C,_1p8),_));return new F(function(){return _1hk(_);});}},_1pe=E(_1gR);if(!_1pe._){var _1pf=B(_1cO(_1gC,_1g4,_));return new F(function(){return _1hj(_);});}else{var _1pg=new T(function(){return B(_I(0,E(_1pe.a),new T(function(){return B(_1gn(_1pe.b));})));}),_1ph=B(_1cO(_1gC,new T2(1,_2C,_1pg),_));return new F(function(){return _1hj(_);});}},_1pi=E(_1gP);if(!_1pi._){var _1pj=B(_1cO(_1gC,_1g4,_));return new F(function(){return _1hi(_);});}else{var _1pk=new T(function(){var _1pl=E(_1pi.a),_1pm=new T(function(){return B(A3(_1cD,_6m,new T2(1,function(_1pn){return new F(function(){return _1gc(_1pl.a,_1pn);});},new T2(1,function(_1po){return new F(function(){return _1gc(_1pl.b,_1po);});},_10)),new T2(1,_G,new T(function(){return B(_1gr(_1pi.b));}))));});return new T2(1,_H,_1pm);}),_1pp=B(_1cO(_1gC,new T2(1,_2C,_1pk),_));return new F(function(){return _1hi(_);});}}else{if(!E(_1ha)){return {_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_sd),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_sd),C:E(_1hb),D:_1hc};}else{var _1pq=B(_1cO(_1gC,_1g3,_)),_1pr=new T(function(){var _1ps=B(_19M(_1h0));return new T2(0,_1ps.a,_1ps.b);}),_1pt=new T(function(){return E(E(_1pr).a);}),_1pu=function(_1pv,_1pw){var _1px=E(_1pv);switch(_1px){case  -2:return {_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_ls),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_ls),C:E(_1hb),D:_1hc};case  -1:var _1py=E(_1gE),_1pz=B(_es(_1py.a,_1py.b,{_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_ls),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_ls),C:E(_1hb),D:_1hc},_));return new T(function(){return {_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(B(_10w(new T(function(){return B(_77(E(_1pr).b,_1h1));})))),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_ls),x:E(_sd),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_sd),C:E(_1hb),D:_1hc};});default:var _1pA=E(_1gE),_1pB=B(_es(_1pA.a,_1pA.b,{_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_ls),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_ls),C:E(_1hb),D:_1hc},_)),_1pC=new T(function(){return (2+E(_1gJ)|0)+3|0;}),_1pD=B(_Gp(_1pA,_G6,_1pC,15+_1gX|0,_1pC,B(_FY(_1gO,_1pt,_1pw)),_));return {_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1px,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_ls),y:E(_1h7),z:E(_sd),A:E(_1h9),B:E(_ls),C:E(_1hb),D:_1hc};}};switch(E(B(_19S(E(_1gF))))){case 32:return new F(function(){return _1pu( -1,_1dY);});break;case 72:var _1pE=E(_1h1);if(!_1pE){var _1pF=B(_7a(_1pt,0))-1|0;return new F(function(){return _1pu(_1pF,_1pF);});}else{var _1pG=_1pE-1|0;return new F(function(){return _1pu(_1pG,_1pG);});}break;case 75:if(_1h1!=(B(_7a(_1pt,0))-1|0)){var _1pH=_1h1+1|0;return new F(function(){return _1pu(_1pH,_1pH);});}else{return new F(function(){return _1pu(0,_1dV);});}break;case 77:var _1pI=E(_1h1);if(!_1pI){var _1pJ=B(_7a(_1pt,0))-1|0;return new F(function(){return _1pu(_1pJ,_1pJ);});}else{var _1pK=_1pI-1|0;return new F(function(){return _1pu(_1pK,_1pK);});}break;case 80:if(_1h1!=(B(_7a(_1pt,0))-1|0)){var _1pL=_1h1+1|0;return new F(function(){return _1pu(_1pL,_1pL);});}else{return new F(function(){return _1pu(0,_1dV);});}break;case 104:if(_1h1!=(B(_7a(_1pt,0))-1|0)){var _1pM=_1h1+1|0;return new F(function(){return _1pu(_1pM,_1pM);});}else{return new F(function(){return _1pu(0,_1dV);});}break;case 106:if(_1h1!=(B(_7a(_1pt,0))-1|0)){var _1pN=_1h1+1|0;return new F(function(){return _1pu(_1pN,_1pN);});}else{return new F(function(){return _1pu(0,_1dV);});}break;case 107:var _1pO=E(_1h1);if(!_1pO){var _1pP=B(_7a(_1pt,0))-1|0;return new F(function(){return _1pu(_1pP,_1pP);});}else{var _1pQ=_1pO-1|0;return new F(function(){return _1pu(_1pQ,_1pQ);});}break;case 108:var _1pR=E(_1h1);if(!_1pR){var _1pS=B(_7a(_1pt,0))-1|0;return new F(function(){return _1pu(_1pS,_1pS);});}else{var _1pT=_1pR-1|0;return new F(function(){return _1pu(_1pT,_1pT);});}break;default:return new F(function(){return _1pu( -2,_1dZ);});}}}};if(!E(_1h5)){return new F(function(){return _1hg(_);});}else{if(!E(_1h6)){return new F(function(){return _Lb(_1gE,_1hf,_1gI,_1gJ,_1gK,_1gL,_1gM,_1gN,_1gO,_1gP,_1gQ,_1gR,_1gS,_1gT,_1gU,_1gV,_1gW,_1gX,_1gY,_1gZ,_1h0,_1h1,_1h2,_1h3,_1h4,_sd,_1h7,_ls,_1h9,_1ha,_1hb,_1hc,_);});}else{return new F(function(){return _1hg(_);});}}}else{return {_:0,a:E(_1hf),b:E(_1he),c:E(_1gK),d:_1gL,e:_1gM,f:_1gN,g:E(_1gO),h:E(_1gP),i:E(_1gQ),j:E(_1gR),k:E(_1gS),l:E(_1hd),m:_1gV,n:_1gW,o:_1gX,p:_1gY,q:_1gZ,r:E(_1h0),s:_1h1,t:E(_1h2),u:E(_1h3),v:E(_1h4),w:E(_1h5),x:E(_1h6),y:E(_1h7),z:E(_ls),A:E(_1h9),B:E(_1ha),C:E(_1hb),D:_1hc};}},_1pU=0,_1pV=2,_1pW=2,_1pX=0,_1pY=new T(function(){return eval("document");}),_1pZ=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1q0=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1q1=function(_1q2){return E(E(_1q2).b);},_1q3=function(_1q4,_1q5){return new F(function(){return A2(_1q1,_1q4,function(_){var _1q6=E(_1q5),_1q7=__app1(E(_1q0),_1q6);if(!_1q7){return _0;}else{var _1q8=__app1(E(_1pZ),_1q6);return new T1(1,new T2(0,_1q8,_1q6));}});});},_1q9=new T2(0,_1dV,_1dV),_1qa=new T(function(){var _1qb=E(_10V);if(!_1qb._){return E(_dJ);}else{return {_:0,a:E(_10R),b:E(_10H),c:E(_1dW),d:E(_1qb.a),e:32,f:0,g:E(_XQ),h:E(_10),i:E(_10),j:E(_10),k:E(_10),l:E(_1q9),m:0,n:0,o:0,p: -1,q:0,r:E(_10),s:0,t:E(_sd),u:E(_sd),v:E(_sd),w:E(_ls),x:E(_sd),y:E(_sd),z:E(_sd),A:E(_sd),B:E(_sd),C:E(_10),D:32};}}),_1qc=new T(function(){return E(E(_1qa).c);}),_1qd=new T(function(){return E(E(E(_1qa).b).a);}),_1qe=new T(function(){return 26-E(_1qd)|0;}),_1qf=new T(function(){return B(unCStr("@"));}),_1qg=new T(function(){return E(E(_1qa).a);}),_1qh=new T(function(){return (E(E(_1qg).b)+2|0)+1|0;}),_1qi=new T(function(){return ((E(E(_1qg).a)+1|0)+26|0)-E(_1qd)|0;}),_1qj=new T1(0,100),_1qk=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/teru/Documents/haskell/haste/fi/Main.hs:12:3-9"));}),_1ql=new T6(0,_0,_2V,_10,_1qk,_0,_0),_1qm=new T(function(){return B(_2T(_1ql));}),_1qn=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/teru/Documents/haskell/haste/fi/Main.hs:13:3-8"));}),_1qo=new T6(0,_0,_2V,_10,_1qn,_0,_0),_1qp=new T(function(){return B(_2T(_1qo));}),_1qq=new T1(1,50),_1qr=function(_1qs,_1qt,_1qu){var _1qv=E(_1qu);if(!_1qv._){return 0;}else{var _1qw=_1qv.b,_1qx=E(_1qv.a),_1qy=_1qx.a,_1qz=_1qx.b;return (_1qs<=_1qy)?1+B(_1qr(_1qs,_1qt,_1qw))|0:(_1qs>=_1qy+_1qx.c)?1+B(_1qr(_1qs,_1qt,_1qw))|0:(_1qt<=_1qz)?1+B(_1qr(_1qs,_1qt,_1qw))|0:(_1qt>=_1qz+_1qx.d)?1+B(_1qr(_1qs,_1qt,_1qw))|0:1;}},_1qA=function(_1qB,_1qC,_1qD){var _1qE=E(_1qD);if(!_1qE._){return 0;}else{var _1qF=_1qE.b,_1qG=E(_1qE.a),_1qH=_1qG.a,_1qI=_1qG.b;if(_1qB<=_1qH){return 1+B(_1qA(_1qB,_1qC,_1qF))|0;}else{if(_1qB>=_1qH+_1qG.c){return 1+B(_1qA(_1qB,_1qC,_1qF))|0;}else{var _1qJ=E(_1qC);return (_1qJ<=_1qI)?1+B(_1qr(_1qB,_1qJ,_1qF))|0:(_1qJ>=_1qI+_1qG.d)?1+B(_1qr(_1qB,_1qJ,_1qF))|0:1;}}}},_1qK=function(_1qL,_1qM,_1qN){var _1qO=E(_1qN);if(!_1qO._){return 0;}else{var _1qP=_1qO.b,_1qQ=E(_1qO.a),_1qR=_1qQ.a,_1qS=_1qQ.b,_1qT=E(_1qL);if(_1qT<=_1qR){return 1+B(_1qA(_1qT,_1qM,_1qP))|0;}else{if(_1qT>=_1qR+_1qQ.c){return 1+B(_1qA(_1qT,_1qM,_1qP))|0;}else{var _1qU=E(_1qM);return (_1qU<=_1qS)?1+B(_1qr(_1qT,_1qU,_1qP))|0:(_1qU>=_1qS+_1qQ.d)?1+B(_1qr(_1qT,_1qU,_1qP))|0:1;}}}},_1qV=new T4(0,100,100,256,367),_1qW=new T2(1,_1qV,_10),_1qX=new T4(0,356,100,100,467),_1qY=new T2(1,_1qX,_1qW),_1qZ=new T4(0,0,0,456,100),_1r0=new T2(1,_1qZ,_1qY),_1r1=new T4(0,0,467,456,100),_1r2=new T2(1,_1r1,_1r0),_1r3=new T4(0,0,100,100,467),_1r4=new T2(1,_1r3,_1r2),_1r5=32,_1r6=76,_1r7=75,_1r8=74,_1r9=72,_1ra=64,_1rb=function(_1rc,_1rd,_1re){var _1rf=new T(function(){switch(B(_1qK(_1rd,_1re,_1r4))){case 1:return E(_1r9);break;case 2:return E(_1r8);break;case 3:return E(_1r7);break;case 4:return E(_1r6);break;case 5:return E(_1r5);break;default:return E(_1ra);}});return function(_1rg,_){var _1rh=E(_1rg),_1ri=E(_1rh.a),_1rj=E(_1rh.b),_1rk=E(_1rh.l);return new F(function(){return _1gD(_1rc,_1rf,_1ri.a,_1ri.b,_1rj.a,_1rj.b,_1rh.c,_1rh.d,_1rh.e,_1rh.f,_1rh.g,_1rh.h,_1rh.i,_1rh.j,_1rh.k,_1rk.a,_1rk.b,_1rh.m,_1rh.n,_1rh.o,_1rh.p,_1rh.q,_1rh.r,_1rh.s,_1rh.t,_1rh.u,_1rh.v,_1rh.w,_1rh.x,_1rh.y,_1rh.z,_1rh.A,_1rh.B,_1rh.C,_1rh.D,_);});};},_1rl=function(_1rm){return E(E(_1rm).a);},_1rn=function(_1ro){return E(E(_1ro).a);},_1rp=function(_1rq){return E(E(_1rq).b);},_1rr=function(_1rs){return E(E(_1rs).b);},_1rt=function(_1ru){return E(E(_1ru).a);},_1rv=function(_){return new F(function(){return nMV(_0);});},_1rw=new T(function(){return B(_3(_1rv));}),_1rx=function(_1ry){return E(E(_1ry).b);},_1rz=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1rA=function(_1rB){return E(E(_1rB).d);},_1rC=function(_1rD,_1rE,_1rF,_1rG,_1rH,_1rI){var _1rJ=B(_1rl(_1rD)),_1rK=B(_1rn(_1rJ)),_1rL=new T(function(){return B(_1q1(_1rJ));}),_1rM=new T(function(){return B(_1rA(_1rK));}),_1rN=new T(function(){return B(A1(_1rE,_1rG));}),_1rO=new T(function(){return B(A2(_1rt,_1rF,_1rH));}),_1rP=function(_1rQ){return new F(function(){return A1(_1rM,new T3(0,_1rO,_1rN,_1rQ));});},_1rR=function(_1rS){var _1rT=new T(function(){var _1rU=new T(function(){var _1rV=__createJSFunc(2,function(_1rW,_){var _1rX=B(A2(E(_1rS),_1rW,_));return _7;}),_1rY=_1rV;return function(_){return new F(function(){return __app3(E(_1rz),E(_1rN),E(_1rO),_1rY);});};});return B(A1(_1rL,_1rU));});return new F(function(){return A3(_1rp,_1rK,_1rT,_1rP);});},_1rZ=new T(function(){var _1s0=new T(function(){return B(_1q1(_1rJ));}),_1s1=function(_1s2){var _1s3=new T(function(){return B(A1(_1s0,function(_){var _=wMV(E(_1rw),new T1(1,_1s2));return new F(function(){return A(_1rr,[_1rF,_1rH,_1s2,_]);});}));});return new F(function(){return A3(_1rp,_1rK,_1s3,_1rI);});};return B(A2(_1rx,_1rD,_1s1));});return new F(function(){return A3(_1rp,_1rK,_1rZ,_1rR);});},_1s4=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1s5=function(_){var _1s6=rMV(E(_1rw)),_1s7=E(_1s6);if(!_1s7._){var _1s8=__app1(E(_1s4),E(_7));return new F(function(){return _7g(_);});}else{var _1s9=__app1(E(_1s4),E(_1s7.a));return new F(function(){return _7g(_);});}},_1sa=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1sb=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1sc=function(_1sd,_1se,_1sf){var _1sg=B(_1rl(_1sd)),_1sh=new T(function(){return B(_1q1(_1sg));}),_1si=function(_1sj){var _1sk=function(_){var _1sl=E(_1se);if(!_1sl._){var _1sm=B(A1(_1sj,_7f)),_1sn=__createJSFunc(0,function(_){var _1so=B(A1(_1sm,_));return _7;}),_1sp=__app2(E(_1sb),_1sl.a,_1sn);return new T(function(){var _1sq=Number(_1sp),_1sr=jsTrunc(_1sq);return new T2(0,_1sr,E(_1sl));});}else{var _1ss=B(A1(_1sj,_7f)),_1st=__createJSFunc(0,function(_){var _1su=B(A1(_1ss,_));return _7;}),_1sv=__app2(E(_1sa),_1sl.a,_1st);return new T(function(){var _1sw=Number(_1sv),_1sx=jsTrunc(_1sw);return new T2(0,_1sx,E(_1sl));});}};return new F(function(){return A1(_1sh,_1sk);});},_1sy=new T(function(){return B(A2(_1rx,_1sd,function(_1sz){return E(_1sf);}));});return new F(function(){return A3(_1rp,B(_1rn(_1sg)),_1sy,_1si);});},_1sA=function(_,_1sB){var _1sC=E(_1sB);if(!_1sC._){return new F(function(){return die(_1qm);});}else{var _1sD=_1sC.a,_1sE=B(A3(_1q3,_5X,_1sD,_)),_1sF=E(_1sE);if(!_1sF._){return new F(function(){return die(_1qp);});}else{var _1sG=E(_1sF.a),_1sH=_1sG.a,_1sI=_1sG.b,_1sJ=B(_dT(_1sH,_1sI,_1qe,_ep,_1qc,_)),_1sK=B(A(_dg,[_1sH,_1dX,_1qi,_1qh,_1qf,_])),_1sL=nMV(_1qa),_1sM=_1sL,_1sN=B(A(_1rC,[_5Y,_3E,_u,_1pY,_1pV,function(_1sO,_){var _1sP=B(_1s5(_)),_1sQ=rMV(_1sM),_1sR=E(_1sQ),_1sS=E(_1sR.a),_1sT=E(_1sR.b),_1sU=E(_1sR.l),_1sV=B(_1gD(_1sG,E(_1sO).a,_1sS.a,_1sS.b,_1sT.a,_1sT.b,_1sR.c,_1sR.d,_1sR.e,_1sR.f,_1sR.g,_1sR.h,_1sR.i,_1sR.j,_1sR.k,_1sU.a,_1sU.b,_1sR.m,_1sR.n,_1sR.o,_1sR.p,_1sR.q,_1sR.r,_1sR.s,_1sR.t,_1sR.u,_1sR.v,_1sR.w,_1sR.x,_1sR.y,_1sR.z,_1sR.A,_1sR.B,_1sR.C,_1sR.D,_)),_=wMV(_1sM,_1sV);return _7f;},_])),_1sW=function(_1sX,_){var _1sY=E(E(_1sX).a),_1sZ=B(_63(_1sI,_)),_1t0=E(_1sZ),_1t1=rMV(_1sM),_1t2=B(A(_1rb,[_1sG,new T(function(){return E(_1sY.a)*E(_1t0.a);},1),new T(function(){return E(_1sY.b)*E(_1t0.b);},1),_1t1,_])),_=wMV(_1sM,_1t2);return _7f;},_1t3=B(A(_1rC,[_5Y,_3E,_3D,_1sD,_1pU,_1sW,_])),_1t4=B(A(_1rC,[_5Y,_3E,_5d,_1sD,_1pX,function(_1t5,_){var _1t6=E(_1t5),_1t7=rMV(_1sM),_1t8=E(_1t7);if(!E(_1t8.y)){var _=wMV(_1sM,_1t8);return _7f;}else{var _1t9=B(_1s5(_)),_=wMV(_1sM,_1t8);return _7f;}},_])),_1ta=function(_){var _1tb=rMV(_1sM),_=wMV(_1sM,new T(function(){var _1tc=E(_1tb);return {_:0,a:E(_1tc.a),b:E(_1tc.b),c:E(_1tc.c),d:_1tc.d,e:_1tc.e,f:_1tc.f,g:E(_1tc.g),h:E(_1tc.h),i:E(_1tc.i),j:E(_1tc.j),k:E(_1tc.k),l:E(_1tc.l),m:_1tc.m,n:_1tc.n,o:_1tc.o,p:_1tc.p,q:_1tc.q,r:E(_1tc.r),s:_1tc.s,t:E(_1tc.t),u:E(_1tc.u),v:E(_1tc.v),w:E(_1tc.w),x:E(_1tc.x),y:E(_sd),z:E(_1tc.z),A:E(_1tc.A),B:E(_1tc.B),C:E(_1tc.C),D:_1tc.D};}));return _7f;},_1td=function(_1te,_){var _1tf=E(_1te),_1tg=rMV(_1sM),_=wMV(_1sM,new T(function(){var _1th=E(_1tg);return {_:0,a:E(_1th.a),b:E(_1th.b),c:E(_1th.c),d:_1th.d,e:_1th.e,f:_1th.f,g:E(_1th.g),h:E(_1th.h),i:E(_1th.i),j:E(_1th.j),k:E(_1th.k),l:E(_1th.l),m:_1th.m,n:_1th.n,o:_1th.o,p:_1th.p,q:_1th.q,r:E(_1th.r),s:_1th.s,t:E(_1th.t),u:E(_1th.u),v:E(_1th.v),w:E(_1th.w),x:E(_1th.x),y:E(_ls),z:E(_1th.z),A:E(_1th.A),B:E(_1th.B),C:E(_1th.C),D:_1th.D};})),_1ti=B(A(_1sc,[_5Y,_1qj,_1ta,_]));return _7f;},_1tj=B(A(_1rC,[_5Y,_3E,_5d,_1sD,_1pW,_1td,_])),_1tk=B(A(_1sc,[_5Y,_1qq,function(_){var _1tl=rMV(_1sM),_1tm=E(_1tl),_1tn=E(_1tm.b),_1to=E(_1tm.l),_1tp=B(_Ig(_1sG,_1tm.a,_1tn.a,_1tn.b,_1tm.c,_1tm.d,_1tm.e,_1tm.f,_1tm.g,_1tm.h,_1tm.i,_1tm.j,_1tm.k,_1to.a,_1to.b,_1tm.m,_1tm.n,_1tm.o,_1tm.p,_1tm.q,_1tm.r,_1tm.s,_1tm.t,_1tm.u,_1tm.v,_1tm.w,_1tm.x,_1tm.y,_1tm.z,_1tm.A,_1tm.B,_1tm.C,_1tm.D,_)),_=wMV(_1sM,_1tp);return _7f;},_]));return _7f;}}},_1tq=function(_){var _1tr=__app1(E(_1),"canvas2"),_1ts=__eq(_1tr,E(_7));if(!E(_1ts)){var _1tt=__isUndef(_1tr);if(!E(_1tt)){return new F(function(){return _1sA(_,new T1(1,_1tr));});}else{return new F(function(){return _1sA(_,_0);});}}else{return new F(function(){return _1sA(_,_0);});}},_1tu=function(_){return new F(function(){return _1tq(_);});};
var hasteMain = function() {B(A(_1tu, [0]));};window.onload = hasteMain;