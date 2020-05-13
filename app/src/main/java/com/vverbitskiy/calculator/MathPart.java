package com.vverbitskiy.calculator;

import java.util.*;

public class MathPart {

    private Operator[] operators;
    private final SortedMap<String, Double> constants;
    private final SortedMap<String, Double> variables;
    private final SortedMap<String, FunctionHandler> pureFunctions;
    private final SortedMap<String, FunctionHandler> impureFunctions;
    private boolean relaxed;
    private String separators;

    private String expression;
    private int offset;
    private boolean isConstant;

    public MathPart() {
        super();

        operators = new Operator[256];
        DefaultImpl.registerOperators(this);

        constants = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
        variables = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
        setConstant("E", Math.E);
        setConstant("Euler", 0.577215664901533D);
        setConstant("LN2", 0.693147180559945D);
        setConstant("LN10", 2.302585092994046D);
        setConstant("LOG2E", 1.442695040888963D);
        setConstant("LOG10E", 0.434294481903252D);
        setConstant("PHI", 1.618033988749895D);
        setConstant("PI", Math.PI);

        pureFunctions = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
        impureFunctions = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
        DefaultImpl.registerFunctions(this);

        relaxed = false;
        separators = null;

        offset = 0;
        isConstant = false;
    }

    public MathPart setConstant(String nam, double val) {
        return setConstant(nam, Double.valueOf(val));
    }

    public MathPart setConstant(String nam, Double val) {
        if (constants.get(nam) != null) {
            throw new IllegalArgumentException("Constants may not be redefined");
        }
        validateName(nam);
        constants.put(nam, val);
        return this;
    }

    public MathPart setOperator(Operator opr) {
        if (opr.symbol >= operators.length) {
            Operator[] noa = new Operator[opr.symbol + (opr.symbol % 255) + 1];
            System.arraycopy(operators, 0, noa, 0, operators.length);
            operators = noa;
        }
        operators[opr.symbol] = opr;
        return this;
    }

    public MathPart setFunctionHandler(String nam, FunctionHandler hdl) {
        return setFunctionHandler(nam, hdl, false);
    }

    public MathPart setFunctionHandler(String nam, FunctionHandler hdl, boolean impure) {
        validateName(nam);
        if (hdl == null) {
            pureFunctions.remove(nam);
            impureFunctions.remove(nam);
        } else if (impure) {
            pureFunctions.remove(nam);
            impureFunctions.put(nam, hdl);
        } else {
            pureFunctions.put(nam, hdl);
            impureFunctions.remove(nam);
        }
        return this;
    }

    public MathPart setVariable(String nam, Double val) {
        validateName(nam);
        if (val == null) {
            variables.remove(nam);
        } else {
            variables.put(nam, val);
        }
        return this;
    }

    private void validateName(String nam) {
        if (!Character.isLetter(nam.charAt(0))) {
            throw new IllegalArgumentException("Names for constants, variables and functions must start with a letter");
        }
        if (nam.indexOf('(') != -1 || nam.indexOf(')') != -1) {
            throw new IllegalArgumentException("Names for constants, variables and functions may not contain a parenthesis");
        }
    }


    public double evaluate(String exp) throws NumberFormatException, ArithmeticException {
        expression = exp;
        isConstant = true;
        offset = 0;
        return _evaluate(0, (exp.length() - 1));
    }

    private double _evaluate(int beg, int end) throws NumberFormatException, ArithmeticException {
        return _evaluate(beg, end, 0.0, OPERAND, getOperator('='));
    }

    private double _evaluate(int beg, int end, double lft, Operator pnd, Operator cur) throws NumberFormatException, ArithmeticException {
        Operator nxt = OPERAND;
        int ofs;

        for (ofs = beg; (ofs = skipWhitespace(expression, ofs, end)) <= end; ofs++) {
            boolean fnc = false;
            double rgt = Double.NaN;

            for (beg = ofs; ofs <= end; ofs++) {
                char chr = expression.charAt(ofs);
                if ((nxt = getOperator(chr)) != OPERAND) {
                    if (nxt.internal) {
                        nxt = OPERAND;
                    } else {
                        break;
                    }
                } else if (chr == ')' || chr == ',') {
                    break;
                }
            }

            EvaluateOperand:
            {
                char ch0 = expression.charAt(beg);
                boolean alp = Character.isLetter(ch0);

                if (cur.unary != LEFT_SIDE) {
                    if (ch0 == '+') {
                        continue;
                    }
                    if (ch0 == '-') {
                        nxt = getOperator('±');
                    }
                }

                if (beg == ofs && (cur.unary == LEFT_SIDE || nxt.unary == RIGHT_SIDE)) {
                    rgt = Double.NaN;
                } else if (ch0 == '(') {
                    rgt = _evaluate(beg + 1, end);
                    ofs = skipWhitespace(expression, offset + 1, end);
                    nxt = (ofs <= end ? getOperator(expression.charAt(ofs)) : OPERAND);
                } else if (alp && nxt.symbol == '(') {
                    rgt = doFunction(beg, end);
                    ofs = skipWhitespace(expression, offset + 1, end);
                    nxt = (ofs <= end ? getOperator(expression.charAt(ofs)) : OPERAND);
                } else if (alp) {
                    rgt = doNamedVal(beg, (ofs - 1));
                } else {
                    try {
                        if (stringOfsEq(expression, beg, "0x")) {
                            rgt = (double) Long.parseLong(expression.substring(beg + 2, ofs).trim(), 16);
                        } else {
                            rgt = Double.parseDouble(expression.substring(beg, ofs).trim());
                        }
                    } catch (NumberFormatException thr) {
                        throw exception(beg, "Invalid numeric value \"" + expression.substring(beg, ofs).trim() + "\"");
                    }
                }
            }

            if (opPrecedence(cur, LEFT_SIDE) < opPrecedence(nxt, RIGHT_SIDE)) {
                rgt = _evaluate((ofs + 1), end, rgt, cur, nxt);
                ofs = offset;
                nxt = (ofs <= end ? getOperator(expression.charAt(ofs)) : OPERAND);
            }

            lft = doOperation(beg, lft, cur, rgt);

            cur = nxt;
            if (opPrecedence(pnd, LEFT_SIDE) >= opPrecedence(cur, RIGHT_SIDE)) {
                break;
            }
            if (cur.symbol == '(') {
                ofs--;
            }
        }
        if (ofs > end && cur != OPERAND) {
            if (cur.unary == LEFT_SIDE) {
                lft = doOperation(beg, lft, cur, Double.NaN);
            } else {
                throw exception(ofs, "Expression ends with a blank operand after operator '" + nxt.symbol + "'");
            }
        }
        offset = ofs;
        return lft;
    }

    private Operator getOperator(char chr) {
        if (chr < operators.length) {
            Operator opr = operators[chr];
            if (opr != null) {
                return opr;
            }
        }
        return OPERAND;
    }

    private int opPrecedence(Operator opr, int sid) {
        if (opr == null) {
            return Integer.MIN_VALUE;
        } else if (opr.unary == NO_SIDE || opr.unary != sid) {
            return (sid == LEFT_SIDE ? opr.precedenceL : opr.precedenceR);
        } else {
            return Integer.MAX_VALUE;
        }
    }

    private double doOperation(int beg, double lft, Operator opr, double rgt) {
        if (opr.unary != RIGHT_SIDE && Double.isNaN(lft)) {
            throw exception(beg, "Mathematical NaN detected in right-operand");
        }
        if (opr.unary != LEFT_SIDE && Double.isNaN(rgt)) {
            throw exception(beg, "Mathematical NaN detected in left-operand");
        }

        try {
            return opr.handler.evaluateOperator(lft, opr.symbol, rgt);
        } catch (ArithmeticException thr) {
            throw exception(beg, "Mathematical expression \"" + expression + "\" failed to evaluate", thr);
        } catch (UnsupportedOperationException thr) {
            int tmp = beg;
            while (tmp > 0 && getOperator(expression.charAt(tmp)) == null) {
                tmp--;
            }
            throw exception(tmp, "Operator \"" + opr.symbol + "\" not handled by math engine (Programmer error: The list of operators is inconsistent within the engine)");
        }
    }

    private double doFunction(int beg, int end) {
        int argbeg;

        for (argbeg = beg; argbeg <= end && expression.charAt(argbeg) != '('; argbeg++) {
            ;
        }

        String fncnam = expression.substring(beg, argbeg).trim();
        ArgParser fncargs = new ArgParser(argbeg, end);
        FunctionHandler fnchdl = null;

        try {
            if ((fnchdl = pureFunctions.get(fncnam)) != null) {
                return fnchdl.evaluateFunction(fncnam, fncargs);
            } else if ((fnchdl = impureFunctions.get(fncnam)) != null) {
                isConstant = false;
                return fnchdl.evaluateFunction(fncnam, fncargs);
            }
            fncargs = null;
        } catch (ArithmeticException thr) {
            fncargs = null;
            throw thr;
        } catch (NoSuchMethodError thr) {
            fncargs = null;
            throw exception(beg, "Function not supported in this JVM: \"" + fncnam + "\"");
        } catch (UnsupportedOperationException thr) {
            fncargs = null;
            throw exception(beg, thr.getMessage());
        } catch (Throwable thr) {
            fncargs = null;
            throw exception(beg, "Unexpected exception parsing function arguments", thr);
        } finally {
            if (fncargs != null) {
                if (fncargs.hasNext()) {
                    throw exception(fncargs.getIndex(), "Function has too many arguments");
                }
                offset = fncargs.getIndex();
            }
        }
        throw exception(beg, "Function \"" + fncnam + "\" not recognized");
    }

    private double doNamedVal(int beg, int end) {
        while (beg < end && Character.isWhitespace(expression.charAt(end))) {
            end--;
        }

        String nam = expression.substring(beg, (end + 1));
        Double val;

        if ((val = constants.get(nam)) != null) {
            return val.doubleValue();
        } else if ((val = variables.get(nam)) != null) {
            isConstant = false;
            return val.doubleValue();
        } else if (relaxed) {
            isConstant = false;
            return 0.0;
        }

        throw exception(beg, "Unrecognized constant or variable \"" + nam + "\"");
    }

    private ArithmeticException exception(int ofs, String txt) {
        return new ArithmeticException(txt + " at offset " + ofs + " in expression \"" + expression + "\"");
    }

    private ArithmeticException exception(int ofs, String txt, Throwable thr) {
        return new ArithmeticException(txt + " at offset " + ofs + " in expression \"" + expression + "\"" + " (Cause: " + (thr.getMessage() != null ? thr.getMessage() : thr.toString()) + ")");
    }

    private boolean stringOfsEq(String str, int ofs, String val) {
        return str.regionMatches(true, ofs, val, 0, val.length());
    }

    private int skipWhitespace(String exp, int ofs, int end) {
        while (ofs <= end && Character.isWhitespace(exp.charAt(ofs))) {
            ofs++;
        }
        return ofs;
    }


    public final class ArgParser {
        final int exEnd;

        int index;

        ArgParser(int excstr, int excend) {
            exEnd = excend;

            index = (excstr + 1);

            index = skipWhitespace(expression, index, exEnd - 1);
        }


        public double next() {
            if (!hasNext()) {
                throw exception(index, "Function has too few arguments");
            }
            return _next();
        }


        public double next(double dft) {
            if (!hasNext()) {
                return dft;
            }
            return _next();
        }

        private double _next() {
            if (expression.charAt(index) == ',') {
                index++;
            }
            double ret = _evaluate(index, exEnd);
            index = offset;
            return ret;
        }


        public boolean hasNext() {
            return (expression.charAt(index) != ')');
        }

        int getIndex() {
            return index;
        }
    }


    static public final class Operator
            extends Object {
        final char symbol;
        final int precedenceL;
        final int precedenceR;
        final int unary;
        final boolean internal;
        final OperatorHandler handler;


        public Operator(char sym, int prc, OperatorHandler hnd) {
            this(sym, prc, prc, NO_SIDE, false, hnd);
        }

        Operator(char sym, int prclft, int prcrgt, int unibnd, boolean intern, OperatorHandler hnd) {
            symbol = sym;
            precedenceL = prclft;
            precedenceR = prcrgt;
            unary = unibnd;
            internal = intern;
            handler = hnd;
        }

        public String toString() {
            return ("MathOperator['" + symbol + "']");
        }
    }


    public interface OperatorHandler {
        double evaluateOperator(double lft, char opr, double rgt) throws ArithmeticException;
    }


    public interface FunctionHandler {
        double evaluateFunction(String fncnam, ArgParser fncargs) throws ArithmeticException;
    }


    static class DefaultImpl
            extends Object
            implements OperatorHandler, FunctionHandler {
        private DefaultImpl() {
        }


        public double evaluateOperator(double lft, char opr, double rgt) {
            switch (opr) {
                case '=':
                    return rgt;
                case '^':
                    return Math.pow(lft, rgt);
                case '±':
                    return -rgt;
                case '*':
                    return lft * rgt;
                case '×':
                    return lft * rgt;
                case '·':
                    return lft * rgt;
                case '(':
                    return lft * rgt;
                case '/':
                    return lft / rgt;
                case '÷':
                    return lft / rgt;
                case '%':
                    return lft % rgt;
                case '+':
                    return lft + rgt;
                case '-':
                    return lft - rgt;
                default:
                    throw new UnsupportedOperationException("MathPart internal operator setup is incorrect - internal operator \"" + opr + "\" not handled");
            }
        }


        public double evaluateFunction(String fncnam, ArgParser fncargs) throws ArithmeticException {
            switch (Character.toLowerCase(fncnam.charAt(0))) {
                case 'a': {
                    if (fncnam.equalsIgnoreCase("abs")) {
                        return Math.abs(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("acos")) {
                        return Math.acos(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("asin")) {
                        return Math.asin(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("atan")) {
                        return Math.atan(fncargs.next());
                    }
                }
                break;
                case 'c': {
                    if (fncnam.equalsIgnoreCase("cbrt")) {
                        return Math.cbrt(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("ceil")) {
                        return Math.ceil(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("cos")) {
                        return Math.cos(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("cosh")) {
                        return Math.cosh(fncargs.next());
                    }
                }
                break;
                case 'e': {
                    if (fncnam.equalsIgnoreCase("exp")) {
                        return Math.exp(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("expm1")) {
                        return Math.expm1(fncargs.next());
                    }
                }
                break;
                case 'f': {
                    if (fncnam.equalsIgnoreCase("floor")) {
                        return Math.floor(fncargs.next());
                    }
                }
                break;
                case 'g': {

                }
                break;
                case 'l': {
                    if (fncnam.equalsIgnoreCase("log")) {
                        return Math.log(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("log10")) {
                        return Math.log10(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("log1p")) {
                        return Math.log1p(fncargs.next());
                    }
                }
                break;
                case 'm': {
                    if (fncnam.equalsIgnoreCase("max")) {
                        return Math.max(fncargs.next(), fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("min")) {
                        return Math.min(fncargs.next(), fncargs.next());
                    }
                }
                break;
                case 'n': {

                }
                break;
                case 'r': {
                    if (fncnam.equalsIgnoreCase("random")) {
                        return Math.random();
                    }
                    if (fncnam.equalsIgnoreCase("round")) {
                        return Math.round(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("roundHE")) {
                        return Math.rint(fncargs.next());
                    }
                }
                break;
                case 's': {
                    if (fncnam.equalsIgnoreCase("signum")) {
                        return Math.signum(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("sin")) {
                        return Math.sin(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("sinh")) {
                        return Math.sinh(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("sqrt")) {
                        return Math.sqrt(fncargs.next());
                    }
                }
                break;
                case 't': {
                    if (fncnam.equalsIgnoreCase("tan")) {
                        return Math.tan(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("tanh")) {
                        return Math.tanh(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("toDegrees")) {
                        return Math.toDegrees(fncargs.next());
                    }
                    if (fncnam.equalsIgnoreCase("toRadians")) {
                        return Math.toRadians(fncargs.next());
                    }
                }
                break;
                case 'u': {
                    if (fncnam.equalsIgnoreCase("ulp")) {
                        return Math.ulp(fncargs.next());
                    }
                }
                break;

            }
            throw new UnsupportedOperationException("MathPart internal function setup is incorrect - internal function \"" + fncnam + "\" not handled");
        }

        static final DefaultImpl INSTANCE = new DefaultImpl();

        static private final Operator OPR_EQU = new Operator('=', 99, 99, RIGHT_SIDE, true, DefaultImpl.INSTANCE);
        static private final Operator OPR_PWR = new Operator('^', 80, 81, NO_SIDE, false, DefaultImpl.INSTANCE);
        static private final Operator OPR_NEG = new Operator('±', 60, 60, RIGHT_SIDE, true, DefaultImpl.INSTANCE);
        static private final Operator OPR_MLT1 = new Operator('*', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_MLT2 = new Operator('×', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_MLT3 = new Operator('·', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_BKT = new Operator('(', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_DIV1 = new Operator('/', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_DIV2 = new Operator('÷', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_MOD = new Operator('%', 40, DefaultImpl.INSTANCE);
        static private final Operator OPR_ADD = new Operator('+', 20, DefaultImpl.INSTANCE);
        static private final Operator OPR_SUB = new Operator('-', 20, DefaultImpl.INSTANCE);


        static void registerOperators(MathPart tgt) {
            tgt.setOperator(OPR_EQU);
            tgt.setOperator(OPR_PWR);
            tgt.setOperator(OPR_NEG);
            tgt.setOperator(OPR_MLT1);
            tgt.setOperator(OPR_MLT2);
            tgt.setOperator(OPR_MLT3);
            tgt.setOperator(OPR_BKT);
            tgt.setOperator(OPR_DIV1);
            tgt.setOperator(OPR_DIV2);
            tgt.setOperator(OPR_MOD);
            tgt.setOperator(OPR_ADD);
            tgt.setOperator(OPR_SUB);
        }


        static void registerFunctions(MathPart tgt) {
            tgt.setFunctionHandler("abs", INSTANCE);
            tgt.setFunctionHandler("acos", INSTANCE);
            tgt.setFunctionHandler("asin", INSTANCE);
            tgt.setFunctionHandler("atan", INSTANCE);
            tgt.setFunctionHandler("cbrt", INSTANCE);
            tgt.setFunctionHandler("ceil", INSTANCE);
            tgt.setFunctionHandler("cos", INSTANCE);
            tgt.setFunctionHandler("cosh", INSTANCE);
            tgt.setFunctionHandler("exp", INSTANCE);
            tgt.setFunctionHandler("expm1", INSTANCE);
            tgt.setFunctionHandler("floor", INSTANCE);

            tgt.setFunctionHandler("log", INSTANCE);
            tgt.setFunctionHandler("log10", INSTANCE);
            tgt.setFunctionHandler("log1p", INSTANCE);
            tgt.setFunctionHandler("max", INSTANCE);
            tgt.setFunctionHandler("min", INSTANCE);

            tgt.setFunctionHandler("random", INSTANCE, true);
            tgt.setFunctionHandler("round", INSTANCE);
            tgt.setFunctionHandler("roundHE", INSTANCE);
            tgt.setFunctionHandler("signum", INSTANCE);
            tgt.setFunctionHandler("sin", INSTANCE);
            tgt.setFunctionHandler("sinh", INSTANCE);
            tgt.setFunctionHandler("sqrt", INSTANCE);
            tgt.setFunctionHandler("tan", INSTANCE);
            tgt.setFunctionHandler("tanh", INSTANCE);
            tgt.setFunctionHandler("toDegrees", INSTANCE);
            tgt.setFunctionHandler("toRadians", INSTANCE);
            tgt.setFunctionHandler("ulp", INSTANCE);
        }
    }


    static public final int LEFT_SIDE = 'L';

    static public final int RIGHT_SIDE = 'R';

    static public final int NO_SIDE = 'B';

    static private final Operator OPERAND = new Operator('\0', 0, 0, NO_SIDE, false, null);


}