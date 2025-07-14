/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.testgen.ReflectionClassCreator;
import de.uka.ilkd.key.testgen.oracle.OracleUnaryTerm.Op;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import com.squareup.javapoet.MethodSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.testgen.Constants.*;
import static de.uka.ilkd.key.testgen.ReflectionClassCreator.*;
import static de.uka.ilkd.key.testgen.TestCaseGenerator.getTypeName;

public class OracleGenerator {
    private static final Logger LOGGER = LoggerFactory.getLogger(OracleGenerator.class);

    private static final String OR = "||";

    private static final String AND = "&&";

    private static final String EQUALS = "==";

    private final Services services;

    private static int varNum;

    private Map<Operator, String> ops = new HashMap<>();

    private final Set<OracleMethod> oracleMethods = new HashSet<>();

    private final List<OracleVariable> quantifiedVariables = new ArrayList<>();

    private Set<String> truePredicates = new TreeSet<>();

    private Set<String> falsePredicates = new TreeSet<>();

    private final Set<String> prestateTerms = new TreeSet<>();

    private final Map<Sort, OracleMethod> invariants = new HashMap<>();

    private List<OracleVariable> methodArgs = new ArrayList<>();

    private Set<Term> constants = new HashSet<>();

    private final ReflectionClassCreator rflCreator;

    private final boolean useRFL;

    public static final String PRE_STRING = "_pre";

    public OracleGenerator(Services services, ReflectionClassCreator rflCreator, boolean useRFL) {
        this.services = services;
        initOps();
        this.rflCreator = rflCreator;
        this.useRFL = useRFL;
        initTrue();
        initFalse();
    }

    private void initTrue() {
        truePredicates = new HashSet<>();
        truePredicates.add("inByte");
        truePredicates.add("inChar");
        truePredicates.add("inShort");
        truePredicates.add("inInt");
        truePredicates.add("inLong");
    }

    private void initFalse() {
        falsePredicates = new HashSet<>();
    }


    private void initOps() {
        ops = new HashMap<>();
        ops.put(Equality.EQV, EQUALS);
        ops.put(Equality.EQUALS, EQUALS);
        ops.put(Junctor.AND, AND);
        ops.put(Junctor.OR, OR);
        ops.put(services.getTypeConverter().getIntegerLDT().getLessOrEquals(), "<=");
        ops.put(services.getTypeConverter().getIntegerLDT().getLessThan(), "<");
        ops.put(services.getTypeConverter().getIntegerLDT().getGreaterOrEquals(), ">=");
        ops.put(services.getTypeConverter().getIntegerLDT().getGreaterThan(), ">");
        ops.put(services.getTypeConverter().getIntegerLDT().getAdd(), "+");
        ops.put(services.getTypeConverter().getIntegerLDT().getArithJavaIntAddition(), "+");
        ops.put(services.getTypeConverter().getIntegerLDT().getSub(), "-");
        ops.put(services.getTypeConverter().getIntegerLDT().getJavaSubInt(), "-");
        ops.put(services.getTypeConverter().getIntegerLDT().getMul(), "*");
        ops.put(services.getTypeConverter().getIntegerLDT().getJavaMulInt(), "*");
        ops.put(services.getTypeConverter().getIntegerLDT().getDiv(), "/");
        ops.put(services.getTypeConverter().getIntegerLDT().getJavaDivInt(), "/");
        ops.put(services.getTypeConverter().getIntegerLDT().getMod(), "%");
        ops.put(services.getTypeConverter().getIntegerLDT().getJavaMod(), "%");
    }

    public OracleMethod generateOracleMethod(Term term) {
        constants = getConstants(term);
        methodArgs = getMethodArgs(term);
        OracleTerm body = generateOracle(term, false);
        return new OracleMethod("testOracle", methodArgs, "return " + body);
    }

    public OracleLocationSet getOracleLocationSet(Term modifierset) {
        ModifiesSetTranslator mst = new ModifiesSetTranslator(services, this);
        return mst.translate(modifierset);
    }

    public Set<OracleMethod> getOracleMethods() {
        return oracleMethods;
    }

    private boolean isRelevantConstant(Term c) {
        Operator op = c.op();

        if (isTrueConstant(op) || isFalseConstant(op)) {
            return false;
        }

        Sort s = c.sort();

        Sort nullSort = services.getJavaInfo().getNullType().getSort();
        Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
        Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        Sort boolSort = services.getTypeConverter().getBooleanLDT().targetSort();

        if (s.equals(nullSort)) {
            return false;
        }
        return s.extendsTrans(objSort) || s.equals(intSort) || s.equals(boolSort);
    }

    private Set<Term> getConstants(Term t) {
        Set<Term> result = new HashSet<>();
        Set<Term> temp = new HashSet<>();
        findConstants(temp, t);
        for (Term c : temp) {
            if (isRelevantConstant(c)) {
                result.add(c);
            }
        }

        return result;
    }


    public Set<Term> getConstants() {
        return constants;
    }

    /* TODO: The argument t is never used? */
    private List<OracleVariable> getMethodArgs(Term t) {

        List<OracleVariable> result = new LinkedList<>();

        Sort allIntSort = createSetSort("Integer");
        Sort allBoolSort = createSetSort("Boolean");
        Sort allObjSort = createSetSort("java.lang.Object");
        Sort oldMapSort = new SortImpl(new Name("Map<Object,Object>"));

        OracleVariable allInts = new OracleVariable(ALL_INTS, allIntSort);
        OracleVariable allBools = new OracleVariable(ALL_BOOLS, allBoolSort);
        OracleVariable allObj = new OracleVariable(ALL_OBJECTS, allObjSort);
        OracleVariable oldMap = new OracleVariable(OLD_MAP, oldMapSort);

        for (Term c : constants) {
            result.add(new OracleVariable(c.op().toString(), c.sort()));
            result.add(new OracleVariable(PRE_STRING + c.op(), c.sort()));
        }

        result.add(allBools);
        result.add(allInts);
        result.add(allObj);
        result.add(oldMap);

        return result;

    }


    private void findConstants(Set<Term> constants, Term term) {
        LOGGER.debug("FindConstants: {} cls {} ", term, term.getClass().getName());
        if (term.op() instanceof Function && term.arity() == 0) {
            constants.add(term);
        }
        if (term.op() instanceof ProgramVariable) {
            constants.add(term);
        }

        for (Term sub : term.subs()) {
            findConstants(constants, sub);
        }
    }

    private Sort createSetSort(String inner) {
        String name = "Set<" + inner + ">";
        return new SortImpl(new Name(name));
    }


    public OracleTerm generateOracle(Term term, boolean initialSelect) {
        Operator op = term.op();

        LOGGER.debug("Translate: {} init: {}", term, initialSelect);

        // binary terms
        if (ops.containsKey(op)) {
            OracleTerm left = generateOracle(term.sub(0), initialSelect);
            OracleTerm right = generateOracle(term.sub(1), initialSelect);
            String javaOp = ops.get(op);
            return switch (javaOp) {
            case EQUALS -> eq(left, right);
            case AND -> and(left, right);
            case OR -> or(left, right);
            default ->
                // Todo wiesler: What is this for? No field nor method of OracleBinTerm has any
                // usages
                new OracleBinTerm(javaOp, left, right);
            };

        } // negation
        else if (op == Junctor.NOT) {
            OracleTerm sub = generateOracle(term.sub(0), initialSelect);
            if (sub instanceof OracleUnaryTerm neg) {
                return neg.sub();
            }
            return new OracleUnaryTerm(sub, Op.Neg);
        }
        // true
        else if (op == Junctor.TRUE) {
            return OracleConstant.TRUE;
        }
        // false
        else if (op == Junctor.FALSE) {
            return OracleConstant.FALSE;
        } else if (op == Junctor.IMP) {
            OracleTerm left = generateOracle(term.sub(0), initialSelect);
            OracleTerm right = generateOracle(term.sub(1), initialSelect);
            OracleTerm notLeft = neg(left);
            return new OracleBinTerm(OR, notLeft, right);
        }
        // quantifiable variable
        else if (op instanceof QuantifiableVariable qop) {
            return new OracleVariable(qop.name().toString(), qop.sort());
        }
        // integers
        else if (op == services.getTypeConverter().getIntegerLDT().getNumberSymbol()) {
            long num = NumberTranslation.translate(term.sub(0)).longValue();
            return new OracleConstant(Long.toString(num), term.sort());
        }
        // forall
        else if (op == Quantifier.ALL || op == Quantifier.EX) {
            Sort field = services.getTypeConverter().getHeapLDT().getFieldSort();
            Sort heap = services.getTypeConverter().getHeapLDT().targetSort();
            Sort varSort = term.boundVars().get(0).sort();
            if (varSort.equals(field) || varSort.equals(heap)) {
                return OracleConstant.TRUE;
            }

            OracleMethod method = createQuantifierMethod(term, initialSelect);
            oracleMethods.add(method);
            List<OracleTerm> args = new LinkedList<>();
            args.addAll(quantifiedVariables);
            args.addAll(methodArgs);
            return new OracleMethodCall(method, args);
        }
        // if-then-else
        else if (op == IfThenElse.IF_THEN_ELSE) {
            OracleMethod method = createIfThenElseMethod(term, initialSelect);
            oracleMethods.add(method);
            List<OracleTerm> args = new LinkedList<>();
            args.addAll(quantifiedVariables);
            args.addAll(methodArgs);
            return new OracleMethodCall(method, args);
        }
        // functions
        else if (op instanceof Function) {
            return translateFunction(term, initialSelect);
        }
        // program variables
        else if (op instanceof ProgramVariable pvar) {
            return new OracleConstant(pvar.name().toString(), pvar.sort());
        } else {
            LOGGER.debug("Could not translate: {}", term);
            throw new RuntimeException(
                "Could not translate oracle for: " + term + " of type " + term.op());
        }

    }

    private OracleTerm translateFunction(Term term, boolean initialSelect) {
        Operator op = term.op();
        Function fun = (Function) op;
        String name = fun.name().toString();
        if (isTrueConstant(op)) {
            return OracleConstant.TRUE;
        } else if (isFalseConstant(op)) {
            return OracleConstant.FALSE;
        } else if (truePredicates.contains(name)) {
            return OracleConstant.TRUE;
        } else if (falsePredicates.contains(name)) {
            return OracleConstant.FALSE;
        } else if (term.arity() == 0) {
            return new OracleConstant(name, term.sort());
        } else if (name.endsWith("select")) {
            return translateSelect(term, initialSelect);
        } else if (name.equals("arr")) {
            OracleTerm index = generateOracle(term.sub(0), initialSelect);
            return new OracleConstant("[" + index + "]", term.sort());
        } else if (name.equals("length")) {
            OracleTerm o = generateOracle(term.sub(0), initialSelect);
            return new OracleConstant(o + ".length", term.sort());
        } else if (name.endsWith("::<inv>")) {
            if (fun instanceof IObserverFunction obs) {

                Sort s = obs.getContainerType().getSort();
                OracleMethod m;

                if (invariants.containsKey(s)) {
                    m = invariants.get(s);
                } else {
                    // needed for recursive invariants
                    m = createDummyInvariant(s);
                    invariants.put(s, m);

                    m = createInvariantMethod(s, initialSelect);
                    invariants.put(s, m);
                    oracleMethods.add(m);
                }

                Term heap = term.sub(0);
                OracleTerm heapTerm = generateOracle(heap, initialSelect);

                Term object = term.sub(1);
                OracleTerm objTerm = generateOracle(object, initialSelect);

                if (isPreHeap(heapTerm) && (!objTerm.toString().startsWith(PRE_STRING))) {
                    prestateTerms.add(objTerm.toString());
                    objTerm = new OracleConstant(PRE_STRING + object, object.sort());
                }

                List<OracleTerm> args = new LinkedList<>();
                args.add(objTerm);
                args.addAll(quantifiedVariables);
                args.addAll(methodArgs);

                return new OracleMethodCall(m, args);
            }
        } else if (name.endsWith("::instance")) {

            if (fun instanceof SortDependingFunction sdf) {
                Sort s = sdf.getSortDependingOn();


                OracleTerm arg = generateOracle(term.sub(0), initialSelect);
                OracleType type = new OracleType(s);

                return new OracleBinTerm("instanceof", arg, type);


            }


        } else if (op instanceof ProgramMethod) {

            return translateQuery(term, initialSelect, op);


        } else if (name.equals("javaUnaryMinusInt")) {
            OracleTerm sub = generateOracle(term.sub(0), initialSelect);
            return new OracleUnaryTerm(sub, Op.Minus);
        }

        throw new RuntimeException(
            "Unsupported function found: " + name + " of type " + fun.getClass().getName());
    }

    private OracleTerm translateQuery(Term term, boolean initialSelect, Operator op) {

        ProgramMethod pm = (ProgramMethod) op;
        OracleMethod m = createDummyOracleMethod(pm);


        List<OracleTerm> params = new LinkedList<>();

        for (int i = pm.isStatic() ? 1 : 2; i < term.subs().size(); i++) {
            OracleTerm param = generateOracle(term.subs().get(i), initialSelect);
            params.add(param);
        }

        LOGGER.info("pm= {}", pm.name());
        for (int i = 0; i < term.arity(); i++) {
            LOGGER.info("(i={}): {}", i, term.sub(i));
        }

        if (pm.isStatic()) {
            LOGGER.info(" isstatic ");
            return new OracleMethodCall(m, params);
        } else {
            OracleTerm caller =
                generateOracle(term.sub(1), false /* TODO: what does this parameter mean? */);
            LOGGER.info(" non-static caller= {}", caller);
            return new OracleMethodCall(m, params, caller);
        }
    }

    private OracleMethod createDummyOracleMethod(ProgramMethod pm) {
        String body = "";
        String methodName;
        if (pm.isStatic()) {
            methodName = pm.name().toString();
            methodName = methodName.replace("::", ".");
        } else {
            methodName = pm.getName();
        }
        Sort returnType = pm.getReturnType().getSort();

        List<OracleVariable> args = new LinkedList<>();


        for (int i = 2; i < pm.argSorts().size(); i++) {
            OracleVariable ovar = new OracleVariable("a" + i, pm.argSorts().get(i));
            args.add(ovar);
        }


        return new OracleMethod(methodName, args, body, returnType);
    }


    private OracleTerm translateSelect(Term term, boolean initialSelect) {
        Term heap = term.sub(0);
        OracleTerm heapTerm = generateOracle(heap, true);

        Term object = term.sub(1);

        OracleTerm objTerm = generateOracle(object, true);


        Term field = term.sub(2);
        OracleTerm fldTerm = generateOracle(field, true);
        String fieldName = fldTerm.toString();
        fieldName = fieldName.substring(fieldName.lastIndexOf(':') + 1);
        fieldName = fieldName.replace("$", "");

        String value;

        value = createLocationString(heapTerm, objTerm, fieldName, object.sort(), term.sort(),
            initialSelect);

        if (!initialSelect && isPreHeap(heapTerm)
                && term.sort().extendsTrans(services.getJavaInfo().getJavaLangObject().getSort())) {
            return new OracleConstant(OLD_MAP + ".get(" + value + ")",
                term.sort());
        }

        return new OracleConstant(value, term.sort());
    }

    private String createLocationString(OracleTerm heapTerm,
            OracleTerm objTerm, String fieldName,
            Sort objSort, Sort fieldSort, boolean initialSelect) {
        String value;
        String objString = objTerm.toString();

        if (isPreHeap(heapTerm)) {
            if (useRFL) {
                if (!objString.startsWith(NAME_OF_CLASS)) {
                    objString = PRE_STRING + objString;
                }
            } else if (initialSelect) {
                objString = PRE_STRING + objString;
            }
        }

        if (fieldName.startsWith("[")) {
            value = objString + fieldName;
        } else {
            if (useRFL) {
                rflCreator.addSort(getTypeName(objSort));

                value = "%s.%s%s(%s.class, %s, \"%s\")".formatted(
                    NAME_OF_CLASS,
                    GET_PREFIX,
                    cleanTypeName(getTypeName(fieldSort)),
                    objSort, objString, fieldName);
            } else {
                value = objString + "." + fieldName;
            }
        }
        return value;
    }

    private boolean isPreHeap(OracleTerm heapTerm) {
        return heapTerm.toString().equals("heapAtPre");
    }

    private boolean isTrueConstant(Operator o) {
        return o.equals(services.getTypeConverter().getBooleanLDT().getTrueConst());
    }

    private boolean isFalseConstant(Operator o) {
        return o.equals(services.getTypeConverter().getBooleanLDT().getFalseConst());
    }

    public static String generateMethodName() {
        varNum++;
        return "sub" + varNum;
    }

    private String getSortInvName(Sort s) {
        String sortName = s.name().toString();
        sortName = sortName.replace(".", "");
        return "inv_" + sortName;
    }

    private OracleMethod createDummyInvariant(Sort s) {
        String methodName = getSortInvName(s);

        List<OracleVariable> args = new LinkedList<>();
        OracleVariable o = new OracleVariable("o", s);
        args.add(o);
        args.addAll(methodArgs);

        String body = "return true";

        return new OracleMethod(methodName, args, body);

    }

    private OracleMethod createInvariantMethod(Sort s, boolean initialSelect) {

        String methodName = getSortInvName(s);

        List<OracleVariable> args = new LinkedList<>();
        OracleVariable o = new OracleVariable("o", s);
        args.add(o);
        args.addAll(methodArgs);
        OracleInvariantTranslator oit = new OracleInvariantTranslator(services);
        Term t = oit.getInvariantTerm(s);

        OracleTerm invTerm = generateOracle(t, initialSelect);

        String body = "return " + invTerm;

        return new OracleMethod(methodName, args, body);


    }

    private OracleMethod createIfThenElseMethod(Term term, boolean initialSelect) {

        String methodName = generateMethodName();
        List<OracleVariable> args = new LinkedList<>(methodArgs);
        OracleTerm cond = generateOracle(term.sub(0), initialSelect);
        OracleTerm trueCase = generateOracle(term.sub(1), initialSelect);
        OracleTerm falseCase = generateOracle(term.sub(2), initialSelect);

        return new OracleMethod(methodName, args, "", term.sort()) {
            @Override
            protected void addBody(MethodSpec.Builder m) {
                m.addComment("return $N ? $L : $L", cond, trueCase, falseCase);
            }
        };
    }

    private String getSetName(Sort s) {

        if (s.equals(JavaDLTheory.FORMULA)) {
            return ALL_BOOLS;
        } else if (s.equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
            return ALL_INTS;
        } else if (s.equals(services.getTypeConverter().getLocSetLDT().targetSort())) {
            throw new RuntimeException("Not implemented yet.");
            // return TestCaseGenerator.ALL_LOCSETS
        } else if (s.equals(services.getTypeConverter().getHeapLDT().getFieldSort())) {
            throw new RuntimeException("Not implemented yet.");
            // return TestCaseGenerator.ALL_FIELDS
        } else if (s.equals(services.getTypeConverter().getHeapLDT().targetSort())) {
            throw new RuntimeException("Not implemented yet.");
            // return TestCaseGenerator.ALL_HEAPS
        } else if (s.equals(services.getTypeConverter().getSeqLDT().targetSort())) {
            throw new RuntimeException("Not implemented yet.");
            // return TestCaseGenerator.ALL_SEQ
        }


        return ALL_OBJECTS;
    }

    private OracleMethod createQuantifierMethod(Term term, boolean initialSelect) {
        String methodName = generateMethodName();
        ImmutableArray<? extends QuantifiableVariable> vars = term.varsBoundHere(0);
        QuantifiableVariable qv = vars.get(0);
        OracleVariable var = new OracleVariable(qv.name().toString(), qv.sort());

        String setName = getSetName(qv.sort());

        quantifiedVariables.add(var);
        OracleTerm sub = generateOracle(term.sub(0), initialSelect);
        quantifiedVariables.remove(var);

        OracleUnaryTerm neg = new OracleUnaryTerm(sub, Op.Neg);

        List<OracleVariable> args = new LinkedList<>();
        args.addAll(quantifiedVariables);
        args.addAll(methodArgs);


        return new OracleMethod(methodName, args, "") {
            @Override
            protected void addBody(MethodSpec.Builder m) {
                if (term.op() == Quantifier.ALL) {
                    createForallBody(m, qv, setName, neg);
                } else if (term.op() == Quantifier.EX) {
                    createExistsBody(m, qv, setName, sub);
                } else {
                    throw new RuntimeException("This is not a quantifier: " + term);
                }
            }
        };
    }

    private void createForallBody(MethodSpec.Builder m, QuantifiableVariable qv, String setName,
            OracleUnaryTerm cond) {
        m
                .beginControlFlow("for($T $N : $N)", getTypeName(qv.sort()), qv.name().toString(),
                    setName)
                .beginControlFlow("if($N)", cond.toString())
                .addStatement("return false")
                .endControlFlow()
                .endControlFlow()
                .addStatement("return true");
    }

    private void createExistsBody(MethodSpec.Builder m, QuantifiableVariable qv, String setName,
            OracleTerm cond) {
        m.beginControlFlow("for($T $N : $N)", getTypeName(qv.sort()), qv.name().toString(), setName)
                .beginControlFlow("if($N)", cond.toString())
                .addStatement("return true")
                .endControlFlow()
                .endControlFlow()
                .addStatement("return false");
    }

    private static OracleTerm neg(OracleTerm t) {
        if (t instanceof OracleUnaryTerm ut) {
            return ut.sub();
        } else {
            return new OracleUnaryTerm(t, Op.Neg);
        }
    }

    private static OracleTerm eq(OracleTerm left, OracleTerm right) {
        if (left.equals(OracleConstant.TRUE)) {
            return right;
        } else if (left.equals(OracleConstant.FALSE)) {
            return neg(right);
        } else if (right.equals(OracleConstant.TRUE)) {
            return left;
        } else if (right.equals(OracleConstant.FALSE)) {
            return neg(left);
        } else {
            return new OracleBinTerm(EQUALS, left, right);
        }
    }

    private static OracleTerm and(OracleTerm left, OracleTerm right) {


        if (left.equals(OracleConstant.TRUE)) {
            return right;
        } else if (left.equals(OracleConstant.FALSE)) {
            return OracleConstant.FALSE;
        } else if (right.equals(OracleConstant.TRUE)) {
            return left;
        } else if (right.equals(OracleConstant.FALSE)) {
            return OracleConstant.FALSE;
        } else {
            return new OracleBinTerm(AND, left, right);
        }


    }

    private static OracleTerm or(OracleTerm left, OracleTerm right) {
        if (left.equals(OracleConstant.TRUE)) {
            return OracleConstant.TRUE;
        } else if (left.equals(OracleConstant.FALSE)) {
            return right;
        } else if (right.equals(OracleConstant.TRUE)) {
            return OracleConstant.TRUE;
        } else if (right.equals(OracleConstant.FALSE)) {
            return left;
        } else {
            return new OracleBinTerm(OR, left, right);
        }
    }
}
