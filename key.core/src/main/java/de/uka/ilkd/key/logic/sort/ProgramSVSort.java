/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.NamedProgramElement;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.DLEmbeddedExpression;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.Intersect;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.expression.operator.adt.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Ccatch;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.ForUpdates;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.DefaultImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Special "sorts" used for schema variables matching program constructs (class ProgramSV). Not
 * really sorts in the theoretical meaning of the word.
 */
public abstract class ProgramSVSort extends SortImpl {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProgramSVSort.class);

    // Keeps the mapping of ProgramSVSort names to
    // ProgramSVSort instances (helpful in parsing
    // schema variable declarations)
    private static final Map<Name, ProgramSVSort> NAME2SORT = new LinkedHashMap<>(60);


    // ----------- Types of Expression Program SVs ----------------------------

    public static final ProgramSVSort LEFTHANDSIDE = new LeftHandSideSort();

    public static final ProgramSVSort VARIABLE = new ProgramVariableSort();

    public static final ProgramSVSort STATICVARIABLE = new StaticVariableSort();

    public static final ProgramSVSort LOCALVARIABLE = new LocalVariableSort();

    public static final ProgramSVSort SIMPLEEXPRESSION = new SimpleExpressionSort();

    public static final ProgramSVSort NONSIMPLEEXPRESSION = new NonSimpleExpressionSort();

    public static final ProgramSVSort NONSIMPLEEXPRESSIONNOCLASSREFERENCE =
        new NonSimpleExpressionNoClassReferenceSort();

    public static final ProgramSVSort EXPRESSION = new ExpressionSort();


    // ----------- Initialisation and Creation expressions -------------------

    public static final ProgramSVSort SIMPLE_NEW = new SimpleNewSVSort();

    public static final ProgramSVSort NONSIMPLE_NEW = new NonSimpleNewSVSort();

    public static final ProgramSVSort NEWARRAY = new NewArraySVSort();

    public static final ProgramSVSort ARRAYINITIALIZER = new ArrayInitializerSVSort();

    public static final ProgramSVSort SPECIALCONSTRUCTORREFERENCE =
        new SpecialConstructorReferenceSort();


    // ----------- Expressions with restrictions on kind of type -------------

    public static final NonSimpleMethodReferenceSort NONSIMPLEMETHODREFERENCE =
        new NonSimpleMethodReferenceSort();


    // ----------- Types of Statement Program SVs -----------------------------

    public static final ProgramSVSort STATEMENT = new StatementSort();

    public static final ProgramSVSort CATCH = new CatchSort();

    public static final ProgramSVSort CCATCH = new CcatchSort();

    public static final ProgramSVSort METHODBODY = new MethodBodySort();

    public static final ProgramSVSort NONMODELMETHODBODY = new NonModelMethodBodySort();

    public static final ProgramSVSort PROGRAMMETHOD = new ProgramMethodSort();

    // -----------Types--------------------------------------------------------

    public static final ProgramSVSort TYPE = new TypeReferenceSort();

    public static final ProgramSVSort TYPENOTPRIMITIVE = new TypeReferenceNotPrimitiveSort();
    public static final ProgramSVSort TYPE_PRIMITIVE = new TypeReferencePrimitiveSort();

    public static final ProgramSVSort CLASSREFERENCE = new MetaClassReferenceSort();


    // -----------Others-------------------------------------------------------

    public static final ProgramSVSort METHODNAME = new MethodNameSort();

    public static final ProgramSVSort LABEL = new LabelSort();


    // -----------Specials for primitive types---------------------------------

    public static final ProgramSVSort JAVABOOLEANEXPRESSION =
        new ExpressionSpecialPrimitiveTypeSort("JavaBooleanExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BOOLEAN });

    public static final ProgramSVSort SIMPLEJAVABYTEEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaByteExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BYTE });

    public static final ProgramSVSort SIMPLEJAVACHAREXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaCharExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_CHAR });

    public static final ProgramSVSort SIMPLEJAVASHORTEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaShortExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_SHORT });

    public static final ProgramSVSort SIMPLEJAVAINTEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaIntExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_INT });

    public static final ProgramSVSort SIMPLEJAVALONGEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaLongExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_LONG });

    public static final ProgramSVSort SIMPLEJAVAFLOATEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaFloatExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_FLOAT });

    public static final ProgramSVSort SIMPLEJAVADOUBLEEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaDoubleExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_DOUBLE });

    public static final ProgramSVSort SIMPLEJAVABYTESHORTEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaByteShortExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BYTE, PrimitiveType.JAVA_SHORT });

    public static final ProgramSVSort SIMPLEJAVABYTESHORTINTEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaByteShortIntExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BYTE, PrimitiveType.JAVA_SHORT,
                PrimitiveType.JAVA_INT });


    public static final ProgramSVSort SIMPLEANYJAVATYPEEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("AnyJavaTypeExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BYTE, PrimitiveType.JAVA_SHORT,
                PrimitiveType.JAVA_INT, PrimitiveType.JAVA_LONG });


    public static final ProgramSVSort SIMPLEANYJAVANUMBERTYPEEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("AnyJavaNumberTypeExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BYTE, PrimitiveType.JAVA_SHORT,
                PrimitiveType.JAVA_INT, PrimitiveType.JAVA_LONG, PrimitiveType.JAVA_CHAR });

    public static final ProgramSVSort SIMPLEJAVASHORTINTLONGEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaShortIntLongExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_SHORT, PrimitiveType.JAVA_INT,
                PrimitiveType.JAVA_LONG });

    public static final ProgramSVSort SIMPLEJAVAINTLONGEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaIntLongExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_INT, PrimitiveType.JAVA_LONG });

    public static final ProgramSVSort SIMPLEJAVACHARBYTESHORTINTEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaCharByteShortIntExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_CHAR, PrimitiveType.JAVA_BYTE,
                PrimitiveType.JAVA_SHORT, PrimitiveType.JAVA_INT });

    public static final ProgramSVSort SIMPLEJAVABIGINTEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("JavaBigintExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BIGINT });


    public static final ProgramSVSort SIMPLEANYNUMBERTYPEEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("AnyNumberTypeExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BYTE, PrimitiveType.JAVA_SHORT,
                PrimitiveType.JAVA_INT, PrimitiveType.JAVA_LONG, PrimitiveType.JAVA_CHAR,
                PrimitiveType.JAVA_BIGINT });

    public static final ProgramSVSort SIMPLEJAVABOOLEANEXPRESSION =
        new SimpleExpressionSpecialPrimitiveTypeSort("SimpleJavaBooleanExpression",
            new PrimitiveType[] { PrimitiveType.JAVA_BOOLEAN });

    public static final ProgramSVSort SIMPLESTRINGEXPRESSION =
        new SimpleExpressionStringSort("SimpleStringExpression");

    public static final ProgramSVSort SIMPLENONSTRINGOBJECTEXPRESSION =
        new SimpleExpressionNonStringObjectSort("SimpleNonStringObjectExpression");


    // --------------- Specials excepting some primitive types--------------

    public static final ProgramSVSort SIMPLEEXPRESSIONNONFLOATDOUBLE =
        new SimpleExpressionExceptingTypeSort("SimpleExpressionNonFloatDouble",
            new PrimitiveType[] { PrimitiveType.JAVA_FLOAT, PrimitiveType.JAVA_DOUBLE });

    // --------------- Specials that can be get rid of perhaps--------------

    public static final ProgramSVSort LOOPINIT = new LoopInitSort();

    public static final ProgramSVSort GUARD = new GuardSort();

    public static final ProgramSVSort FORUPDATES = new ForUpdatesSort();

    public static final ProgramSVSort FORLOOP = new ForLoopSort();

    public static final ProgramSVSort MULTIPLEVARDECL = new MultipleVariableDeclarationSort();

    public static final ProgramSVSort ARRAYPOSTDECL = new ArrayPostDeclarationSort();

    public static final ProgramSVSort SWITCH = new SwitchSVSort();

    public static final ProgramSVSort CONSTANT_PRIMITIVE_TYPE_VARIABLE =
        new ConstantProgramVariableSort(new Name("ConstantPrimitiveTypeVariable"), false);

    public static final ProgramSVSort CONSTANT_STRING_VARIABLE =
        new ConstantProgramVariableSort(new Name("ConstantStringVariable"), true);


    public static final ProgramSVSort VARIABLEINIT =
        new ProgramSVSort(new Name("VariableInitializer")) {
            @Override
            public boolean canStandFor(ProgramElement pe, Services services) {
                return true;
            }
        };

    public static final ProgramSVSort NONSTRINGLITERAL = new NonStringLiteralSort();
    public static final ProgramSVSort STRINGLITERAL = new StringLiteralSort();

    // --------------- Specials that match on certain names-----------------

    public static final ProgramSVSort ARRAYLENGTH = new ArrayLengthSort();

    // ---------------REFERENCE SORTS ------------------------
    public static final ProgramSVSort EXECUTIONCONTEXT = new ExecutionContextSort();

    // --------------------------------------------------------------------------

    public ProgramSVSort(Name name) {
        super(name, DefaultImmutableSet.nil(), false, "", "");
        NAME2SORT.put(name, this);
    }

    public boolean canStandFor(Term t) {
        return true;
    }

    public boolean canStandFor(ProgramElement check, ExecutionContext ec, Services services) {
        return canStandFor(check, services);
    }


    protected abstract boolean canStandFor(ProgramElement check, Services services);


    public ProgramSVSort createInstance(String parameter) {
        throw new UnsupportedOperationException();
    }

    // -------------Now the inner classes representing the-----------------------
    // -------------different kinds of program SVs-------------------------------

    /**
     * This sort represents a type of program schema variables that match only on
     * <ul>
     * <li>program variables or
     * <li>static field references with a prefix that consists of
     * <ul>
     * <li>a program variable followed by a sequence of attribute accesses or
     * <li>of a type reference followed by a sequence of attribute accesses
     * </ul>
     * </ul>
     */
    private static class LeftHandSideSort extends ProgramSVSort {

        public LeftHandSideSort() {
            super(new Name("LeftHandSide"));
        }

        public LeftHandSideSort(Name name) {
            super(name);
        }

        @Override
        public boolean canStandFor(Term t) {
            return t.op() instanceof ProgramVariable;
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            if (pe instanceof ProgramVariable || pe instanceof ThisReference
                    || pe instanceof VariableSpecification) {
                return true;
            }

            if (pe instanceof FieldReference fr) {

                // we allow only static field references with a
                // sequence of PVs or TypeRef
                ReferencePrefix rp = fr.getReferencePrefix();
                if ((fr.getProgramVariable()).isStatic()) {
                    return (rp == null || rp instanceof ThisReference || rp instanceof TypeReference
                            || canStandFor(rp, services));
                }
            }
            return false;
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on
     * <ul>
     * <li>program variables or
     * <li>static field references with a prefix that consists of
     * <ul>
     * <li>a program variable followed by a sequence of attribute accesses or
     * <li>of a type reference followed by a sequence of attribute accesses
     * </ul>
     * </ul>
     * . In opposite to its super class it matches only if the field reference does not trigger
     * static initialisation (i.e. if it is no active reference)
     */
    private static class ProgramVariableSort extends LeftHandSideSort {

        public ProgramVariableSort() {
            super(new Name("Variable"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            ProgramVariable accessedField = null;
            if (pe instanceof FieldReference) {
                accessedField = ((FieldReference) pe).getProgramVariable();
            } else if (pe instanceof ProgramVariable) {
                accessedField = (ProgramVariable) pe;
            }

            if (accessedField != null && accessedField.isStatic()
                    && !(accessedField instanceof ProgramConstant)) {
                return false;
            }
            return super.canStandFor(pe, services);
        }

    }


    private static class StaticVariableSort extends LeftHandSideSort {

        public StaticVariableSort() {
            super(new Name("StaticVariable"));
        }

        @Override
        public boolean canStandFor(Term t) {
            return t.op() instanceof ProgramVariable && ((ProgramVariable) t.op()).isStatic();
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            ProgramVariable accessedField = null;
            if (pe instanceof FieldReference) {
                accessedField = ((FieldReference) pe).getProgramVariable();
            } else if (pe instanceof ProgramVariable) {
                accessedField = (ProgramVariable) pe;
            }
            if (accessedField != null) {
                return accessedField.isStatic() && !(accessedField instanceof ProgramConstant)
                        && super.canStandFor(pe, services);
            }
            return false;
        }

    }

    private static class LocalVariableSort extends LeftHandSideSort {

        public LocalVariableSort() {
            super(new Name("LocalVariable"));
        }

        @Override
        public boolean canStandFor(Term t) {
            return t.op() instanceof ProgramVariable && !((ProgramVariable) t.op()).isStatic();
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return pe instanceof ProgramVariable && !((ProgramVariable) pe).isStatic();
        }

    }


    /**
     * This sort represents a type of program schema variables that match only on
     * <ul>
     * <li>program variables or
     * <li>static field references with a prefix that consists of
     * <ul>
     * <li>a program variable followed by a sequence of attribute accesses or
     * <li>of a type reference followed by a sequence of attribute accesses
     * </ul>
     * <li>(negated) literal expressions or
     * <li>instanceof expressions v instanceof T with an expression v that matches on a program
     * variable SV
     * </ul>
     */
    private static class SimpleExpressionSort extends ProgramSVSort {

        public SimpleExpressionSort() {
            super(new Name("SimpleExpression"));
        }

        protected SimpleExpressionSort(Name n) {
            super(n);
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            if (pe instanceof Negative) {
                return ((Negative) pe).getChildAt(0) instanceof Literal;
            }

            if (pe instanceof StringLiteral) {
                return false;
            }

            if (pe instanceof Literal) {
                return true;
            }

            if (pe instanceof Instanceof) {
                ProgramElement v = ((Instanceof) pe).getChildAt(0);
                return VARIABLE.canStandFor(v, services);
            }

            if (pe instanceof SetUnion || pe instanceof Singleton || pe instanceof Intersect
                    || pe instanceof SetMinus || pe instanceof AllFields || pe instanceof AllObjects
                    || pe instanceof SeqSingleton || pe instanceof SeqConcat
                    || pe instanceof SeqLength || pe instanceof SeqGet || pe instanceof SeqIndexOf
                    || pe instanceof SeqSub || pe instanceof SeqReverse || pe instanceof SeqPut) {
                if (pe instanceof NonTerminalProgramElement npe) {
                    for (int i = 0, childCount = npe.getChildCount(); i < childCount; i++) {
                        if (!canStandFor(npe.getChildAt(i), services)) {
                            return false;
                        }
                    }
                }
                return true;
            } else if (pe instanceof DLEmbeddedExpression) {
                // this is a not so nice special case (all expressions within
                // embedded expressions are considered to be side effect free;
                // to handle it properly we need some meta constructs to
                // decompose these expressions
                return true;
            }
            return VARIABLE.canStandFor(pe, services);
        }
    }


    private static class NonSimpleExpressionNoClassReferenceSort extends NonSimpleExpressionSort {

        public NonSimpleExpressionNoClassReferenceSort() {
            super(new Name("NonSimpleExpressionNoClassReference"));
        }

        /* Will not match on MetaClassReference variables */
        @Override
        public boolean canStandFor(ProgramElement check, Services services) {
            return super.canStandFor(check, services)
                    && !CLASSREFERENCE.canStandFor(check, services);
        }
    }


    /**
     * This sort represents a type of program schema variables that match only on all expressions
     * which are not matched by simple expression SVs.
     */
    private static class NonSimpleExpressionSort extends ProgramSVSort {

        public NonSimpleExpressionSort() {
            super(new Name("NonSimpleExpression"));
        }

        protected NonSimpleExpressionSort(Name n) {
            super(n);
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            if (!(check instanceof Expression) || check instanceof SuperReference) {
                return false;
            }
            return !SIMPLEEXPRESSION.canStandFor(check, services);
        }
    }

    /**
     * This sort represents a type of program schema variables that match on all expressions only.
     */
    private static class ExpressionSort extends ProgramSVSort {

        public ExpressionSort() {
            super(new Name("Expression"));
        }

        protected ExpressionSort(Name n) {
            super(n);
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Expression);
        }

    }

    /**
     * This sort represents a type of program schema variables that match only string literals, e.g.
     * "abc"
     */
    private static class StringLiteralSort extends ProgramSVSort {
        public StringLiteralSort() {
            super(new Name("StringLiteral"));
        }

        protected StringLiteralSort(Name n) {
            super(n);
        }

        // do not match a term
        @Override
        public boolean canStandFor(Term t) {
            return false;
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof StringLiteral);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on non-string
     * literals
     */
    private static class NonStringLiteralSort extends ProgramSVSort {

        public NonStringLiteralSort() {
            super(new Name("NonStringLiteral"));
        }

        protected NonStringLiteralSort(Name n) {
            super(n);
        }

        // not designed to match on terms
        @Override
        public boolean canStandFor(Term t) {
            return false;
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Literal && !(pe instanceof StringLiteral));
        }
    }


    // ----------- Initialisation and Creation expressions -------------------


    /**
     * This sort represents a type of program schema variables that match only on Class Instance
     * Creation Expressions, new C(), where all arguments are simple expressions.
     */
    private static class SimpleNewSVSort extends ProgramSVSort {

        public SimpleNewSVSort() {
            super(new Name("SimpleInstanceCreation"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            if (!(check instanceof New)) {
                return false;
            }
            for (Expression arg : ((New) check).getArguments()) {
                if (NONSIMPLEEXPRESSION.canStandFor(arg, services)) {
                    return false;
                }
            }
            return true;
        }
    }


    /**
     * This sort represents a type of program schema variables that match only on Class Instance
     * Creation Expressions, new C(), where at least one argument is a non-simple expression
     */
    private static class NonSimpleNewSVSort extends ProgramSVSort {

        public NonSimpleNewSVSort() {
            super(new Name("NonSimpleInstanceCreation"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            if (!(check instanceof New)) {
                return false;
            }
            for (Expression arg : ((New) check).getArguments()) {
                if (NONSIMPLEEXPRESSION.canStandFor(arg, services)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on Array Creation
     * Expressions, new A[]
     */
    private static class NewArraySVSort extends ProgramSVSort {
        public NewArraySVSort() {
            super(new Name("ArrayCreation"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof NewArray);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on Array
     * Initializers.
     */
    private static final class ArrayInitializerSVSort extends ProgramSVSort {

        public ArrayInitializerSVSort() {
            super(new Name("ArrayInitializer"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof ArrayInitializer);
        }
    }


    /**
     * This sort represents a type of program schema variables that match only on Special
     * Constructor References.
     */
    private static class SpecialConstructorReferenceSort extends ProgramSVSort {

        public SpecialConstructorReferenceSort() {
            super(new Name("SpecialConstructorReference"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof SpecialConstructorReference);
        }

        @Override
        public boolean canStandFor(Term t) {
            return (t.op() instanceof IProgramMethod && !((IProgramMethod) t.op()).isModel());
        }
    }



    // ----------- Types of Statement Program SVs -----------------------------

    /**
     * This sort represents a type of program schema variables that match only on statements
     */
    private static class StatementSort extends ProgramSVSort {
        public StatementSort() {
            super(new Name("Statement"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Statement);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on catch branches of
     * try-catch-finally blocks
     */
    private static final class CatchSort extends ProgramSVSort {

        public CatchSort() {
            super(new Name("Catch"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Catch);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on ccatch branches of
     * exec blocks
     */
    private static final class CcatchSort extends ProgramSVSort {

        public CcatchSort() {
            super(new Name("Ccatch"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Ccatch);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on method body
     * statements
     */
    private static final class MethodBodySort extends ProgramSVSort {
        public MethodBodySort() {
            super(new Name("MethodBody"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof MethodBodyStatement);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on method body
     * statements for nonmodel methods for which an implementation is present.
     */
    private static final class NonModelMethodBodySort extends ProgramSVSort {

        public NonModelMethodBodySort() {
            super(new Name("NonModelMethodBody"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            if (!(pe instanceof MethodBodyStatement)) {
                return false;
            }

            final IProgramMethod pm = ((MethodBodyStatement) pe).getProgramMethod(services);
            if (pm == null) {
                return false;
            }
            final MethodDeclaration methodDeclaration = pm.getMethodDeclaration();

            return !(// pm.isModel() ||
            methodDeclaration.getBody() == null)
                    || (methodDeclaration instanceof ConstructorDeclaration);
        }

    }

    /**
     * This sort represents a type of program schema variables that match on a method call with
     * SIMPLE PREFIX and AT LEAST a NONSIMPLE expression in the ARGUMENTS.
     */
    private static final class NonSimpleMethodReferenceSort extends ProgramSVSort {

        public NonSimpleMethodReferenceSort() {
            super(new Name("NonSimpleMethodReference"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            if (pe instanceof MethodReference mr) {
                // FIX to bug #1223 (according to CS)
                /*
                 * if (mr.getReferencePrefix() instanceof SuperReference || mr.getReferencePrefix()
                 * instanceof TypeReference) { return false; }
                 */
                if (mr.getReferencePrefix() != null
                        && NONSIMPLEEXPRESSION.canStandFor(mr.getReferencePrefix(), services)) {
                    return false;
                }
                if (mr.getArguments() == null) {
                    return false;
                }
                for (int i = 0; i < mr.getArguments().size(); i++) {
                    if (NONSIMPLEEXPRESSION.canStandFor(mr.getArgumentAt(i), services)) {
                        return true;
                    }
                }
            }
            return false;
        }

        @Override
        public boolean canStandFor(Term t) {
            return (t.op() instanceof IProgramMethod);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on program methods
     */
    private static final class ProgramMethodSort extends ProgramSVSort {

        public ProgramMethodSort() {
            super(new Name("ProgramMethod"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof IProgramMethod);
        }
    }

    // -----------Types--------------------------------------------------------

    /**
     * This sort represents a type of program schema variables that match only on type references.
     */
    private static final class TypeReferenceSort extends ProgramSVSort {
        public TypeReferenceSort() {
            super(new Name("Type"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof TypeReference);
        }
    }

    /**
     * This sort represents a type of program schema variables that matches byte,
     * char, short, int, and long.
     */
    private static final class TypeReferencePrimitiveSort extends ProgramSVSort {
        public TypeReferencePrimitiveSort() {
            super(new Name("PrimitiveType"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            if (!(check instanceof TypeReference)) {
                return false;
            }
            return ((TypeReference) (check)).getKeYJavaType()
                    .getJavaType() instanceof PrimitiveType;
        }

        @Override
        public ProgramSVSort createInstance(String parameter) {
            return TYPE_PRIMITIVE;
        }
    }


    /**
     * This sort represents a type of program schema variables that match anything except byte,
     * char, short, int, and long.
     */
    private static final class TypeReferenceNotPrimitiveSort extends ProgramSVSort {
        private final String matchName;

        public TypeReferenceNotPrimitiveSort() {
            super(new Name("NonPrimitiveType"));
            this.matchName = null;
        }

        public TypeReferenceNotPrimitiveSort(String name) {
            super(new Name("NonPrimitiveType" + (name != null ? "[name=" + name + "]" : "")));
            this.matchName = name;
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            if (!(check instanceof TypeReference)) {
                return false;
            }
            if (((TypeReference) (check)).getKeYJavaType().getJavaType() instanceof PrimitiveType) {
                return false;
            }
            if (matchName != null) {
                return matchName.equals(
                    ((TypeReference) (check)).getKeYJavaType().getJavaType().getFullName());
            }
            return true;
        }

        @Override
        public ProgramSVSort createInstance(String parameter) {
            return new TypeReferenceNotPrimitiveSort(parameter);
        }
    }

    /**
     * This sort represents a type of program schema variables that match only on meta class
     * references.
     */
    private static final class MetaClassReferenceSort extends ProgramSVSort {

        public MetaClassReferenceSort() {
            super(new Name("ClassReference"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof MetaClassReference);
        }
    }


    // -----------Names--------------------------------------------------------

    /**
     * This sort represents a type of program schema variables that match on names of method
     * references, i.e. the "m" of o.m(p1,pn).
     *
     * It can also be made to match only specific method names defined by the parameter "name".
     */
    private static class MethodNameSort extends ProgramSVSort {
        private final ProgramElementName methodName;

        public MethodNameSort() {
            super(new Name("MethodName"));
            this.methodName = null;
        }

        public MethodNameSort(ProgramElementName name) {
            super(new Name("MethodName" + (name != null ? "[name=" + name + "]" : "")));
            this.methodName = name;
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            if (pe instanceof MethodName) {
                return methodName == null || pe.equals(methodName);
            }
            return false;
        }

        @Override
        public ProgramSVSort createInstance(String parameter) {
            return new MethodNameSort(new ProgramElementName(parameter));
        }

        @Override
        public String declarationString() {
            return name().toString();
        }

    }

    /**
     * This sort represents a type of program schema variables that match on labels.
     */
    private static final class LabelSort extends ProgramSVSort {
        public LabelSort() {
            super(new Name("Label"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Label);
        }
    }


    /**
     * This sort represents a type of program schema variables that match on string literals and
     * string variables.
     */
    public static final class SimpleExpressionStringSort extends SimpleExpressionSort {
        public SimpleExpressionStringSort(String name) {
            super(new Name(name));
        }

        /* Will only match on String variables */
        @Override
        public boolean canStandFor(ProgramElement check, ExecutionContext ec, Services services) {
            if (!super.canStandFor(check, ec, services)) {
                return false;
            }
            // String Literal has SideEffects, but SimpleExpressionSort will not match
            // if (check instanceof StringLiteral) return false;
            if (check instanceof ProgramVariable) {
                Namespace<Sort> ns = services.getNamespaces().sorts();
                Sort stringSort = ns.lookup(new Name("java.lang.String"));
                return ((ProgramVariable) check).getKeYJavaType().getSort().equals(stringSort);
            }
            return false;
        }
    }


    /**
     * This sort represents a type of program schema variables that match on non string object
     * variables.
     */
    public static class SimpleExpressionNonStringObjectSort extends SimpleExpressionSort {
        public SimpleExpressionNonStringObjectSort(String name) {
            super(new Name(name));
        }

        @Override
        public boolean canStandFor(ProgramElement check, ExecutionContext ec, Services services) {
            if (!super.canStandFor(check, ec, services)) {
                return false;
            }
            if (check instanceof ProgramVariable) {
                final Sort checkSort = ((ProgramVariable) check).sort();
                Namespace<Sort> ns = services.getNamespaces().sorts();
                Sort stringSort = ns.lookup(new Name("java.lang.String"));
                return checkSort.extendsTrans(services.getJavaInfo().objectSort())
                        && !checkSort.equals(stringSort);
            }
            return false;
        }
    }

    // -----------Specials for primitive types---------------------------------


    /**
     * This sort represents a type of program schema variables that match on simple expressions
     * which have a special primitive type.
     */
    private static final class SimpleExpressionSpecialPrimitiveTypeSort
            extends SimpleExpressionSort {

        private final PrimitiveType[] allowedPrimitiveTypes;

        public SimpleExpressionSpecialPrimitiveTypeSort(String name, PrimitiveType[] allowedTypes) {
            super(new Name(name));
            this.allowedPrimitiveTypes = allowedTypes;
        }

        @Override
        public boolean canStandFor(ProgramElement check, ExecutionContext ec, Services services) {
            if (!super.canStandFor(check, ec, services)) {
                return false;
            }
            final KeYJavaType kjt = getKeYJavaType(check, ec, services);
            if (kjt != null) {
                final Type type = kjt.getJavaType();
                for (PrimitiveType allowedType : allowedPrimitiveTypes) {
                    if (type == allowedType) {
                        return true;
                    }
                }
            }
            return false;
        }
    }

    /**
     * This sort represents a type of program schema variables that match on simple expressions,
     * except if they match a special primitive type.
     */
    private static final class SimpleExpressionExceptingTypeSort extends SimpleExpressionSort {

        private final PrimitiveType[] forbidden_types;

        public SimpleExpressionExceptingTypeSort(String name, PrimitiveType[] forbidden_types) {

            super(new Name(name));
            this.forbidden_types = forbidden_types;
        }

        public boolean canStandFor(ProgramElement check, ExecutionContext ec, Services services) {
            if (!super.canStandFor(check, ec, services)) {
                return false;
            }
            final KeYJavaType kjt = getKeYJavaType(check, ec, services);
            if (kjt != null) {
                final Type type = kjt.getJavaType();
                for (PrimitiveType forbidden_type : forbidden_types) {
                    if (type == forbidden_type) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    /**
     * This sort represents a type of program schema variables that match on simple expressions
     * which have a special primitive type.
     */
    private static final class ExpressionSpecialPrimitiveTypeSort extends ExpressionSort {

        private final PrimitiveType[] allowedPrimitiveTypes;

        public ExpressionSpecialPrimitiveTypeSort(String name, PrimitiveType[] allowedTypes) {
            super(new Name(name));
            this.allowedPrimitiveTypes = allowedTypes;
        }

        @Override
        public boolean canStandFor(ProgramElement check, ExecutionContext ec, Services services) {
            if (!super.canStandFor(check, ec, services)) {
                return false;
            }

            final KeYJavaType kjt = getKeYJavaType(check, ec, services);
            if (kjt != null) {
                final Type type = kjt.getJavaType();

                for (PrimitiveType allowedType : allowedPrimitiveTypes) {
                    if (type == allowedType) {
                        return true;
                    }
                }
            }
            return false;
        }
    }

    // -----------Specials (unnecessary?)--------------------------------------


    private static final class LoopInitSort extends ProgramSVSort {

        public LoopInitSort() {
            super(new Name("LoopInit"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof LoopInit);
        }
    }

    private static final class GuardSort extends ProgramSVSort {
        public GuardSort() {
            super(new Name("Guard"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof Guard);
        }
    }

    private static final class ForUpdatesSort extends ProgramSVSort {
        public ForUpdatesSort() {
            super(new Name("ForUpdates"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof ForUpdates);

        }
    }

    private static final class ForLoopSort extends ProgramSVSort {

        public ForLoopSort() {
            super(new Name("ForLoop"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof For);
        }
    }

    private static final class SwitchSVSort extends ProgramSVSort {

        public SwitchSVSort() {
            super(new Name("Switch"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return (pe instanceof Switch);
        }
    }

    private static final class MultipleVariableDeclarationSort extends ProgramSVSort {

        public MultipleVariableDeclarationSort() {
            super(new Name("MultipleVariableDeclaration"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return pe instanceof VariableDeclaration
                    && ((VariableDeclaration) pe).getVariables().size() > 1;
        }
    }

    private static final class ArrayPostDeclarationSort extends ProgramSVSort {

        public ArrayPostDeclarationSort() {
            super(new Name("ArrayPostDeclaration"));
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return pe instanceof VariableDeclaration
                    && ((VariableDeclaration) pe).getVariables().size() == 1
                    && ((VariableDeclaration) pe).getVariables().get(0).getDimensions() > 0;

        }

    }


    // ------------------ stuff concerned with explicit and implicit elements----


    private static final class ConstantProgramVariableSort extends ProgramSVSort {

        private final Name type = new Name("java.lang.String");
        private final boolean isString;

        public ConstantProgramVariableSort(Name svSortName, boolean string) {
            super(svSortName);
            isString = string;
        }

        @Override
        public boolean canStandFor(Term t) {
            return t.op() instanceof ProgramConstant && isString == t.sort().name().equals(type);
        }

        @Override
        protected boolean canStandFor(ProgramElement pe, Services services) {
            return false;
        }
    }

    private static final class ArrayLengthSort extends ProgramSVSort {

        public ArrayLengthSort() {
            super(new Name("ArrayLength"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            if (check instanceof ProgramVariable) {
                return check == services.getJavaInfo().getArrayLength();
            }
            return false;
        }
    }

    private static final class ExecutionContextSort extends ProgramSVSort {

        public ExecutionContextSort() {
            super(new Name("ExecutionContext"));
        }

        @Override
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof ExecutionContext);
        }
    }


    // -------------------helper methods ------------------------------------

    static boolean methodConstrReference(ProgramElement pe) {
        return (pe instanceof MethodReference) || (pe instanceof ConstructorReference);
    }

    public ProgramElement getSVWithSort(ExtList l, Class<?> alternative) {
        for (final Object o : l) {
            if (o instanceof SchemaVariable && (((SchemaVariable) o).sort() == this)) {
                return (ProgramElement) o;
            } else if ((alternative.isInstance(o)) && (!(o instanceof SchemaVariable))) {
                return (ProgramElement) o;
            }
        }
        return null;
    }

    static KeYJavaType getKeYJavaType(ProgramElement pe, ExecutionContext ec, Services services) {
        return services.getTypeConverter().getKeYJavaType((Expression) pe, ec);
    }

    static boolean implicit(ProgramElement pe) {
        if (pe instanceof ProgramVariable) {
            if (!((ProgramVariable) pe).isMember()) {
                return false;
            }
        }

        final String elemname;
        if (pe instanceof NamedProgramElement) {
            elemname = ((NamedProgramElement) pe).getProgramElementName().getProgramName();
        } else if (pe instanceof Named) {
            final Name n = ((Named) pe).name();
            if (n instanceof ProgramElementName) {
                elemname = ((ProgramElementName) n).getProgramName();
            } else {
                elemname = n.toString();
            }
        } else {
            LOGGER.warn("Please check implicit in ProgramSVSort");
            return false;
        }
        return elemname.charAt(0) == '<';
    }

    public static Map<Name, ProgramSVSort> name2sort() {
        return NAME2SORT;
    }

}
