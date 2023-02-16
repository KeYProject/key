package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.*;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;
import org.key_project.util.collection.ImmutableArray;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A configurable pretty printer for Java source elements originally from COMPOST.
 *
 * @author AL
 *
 *         CHANGED FOR KeY. Comments are not printed!
 */
public class PrettyPrinter implements Visitor {
    private static final Logger LOGGER = LoggerFactory.getLogger(PrettyPrinter.class);

    protected final PosTableLayouter l;

    protected boolean startAlreadyMarked = false;
    protected Object firstStatement = null;
    protected boolean endAlreadyMarked = false;

    protected SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /** creates a new PrettyPrinter */
    public PrettyPrinter(PosTableLayouter out) {
        l = out;
    }

    public PrettyPrinter(PosTableLayouter o, SVInstantiations svi) {
        this(o);
        this.instantiations = svi;
    }

    /**
     * Marks the start of the first executable statement ...
     *
     * @param stmt current statement;
     */
    protected void markStart(Object stmt) {
        if (!startAlreadyMarked) {
            l.mark(PosTableLayouter.MarkType.MARK_START_FIRST_STMT);
            firstStatement = stmt;
            startAlreadyMarked = true;
        }
    }

    /**
     * Marks the end of the first executable statement ...
     */
    protected void markEnd(Object stmt) {
        if (!endAlreadyMarked && (firstStatement == stmt)) {
            l.mark(PosTableLayouter.MarkType.MARK_END_FIRST_STMT);
            endAlreadyMarked = true;
        }
    }

    /**
     * Replace all unicode characters above ? by their explicit representation.
     *
     * @param str the input string.
     * @return the encoded string.
     */
    protected static String encodeUnicodeChars(String str) {
        int len = str.length();
        StringBuilder buf = new StringBuilder(len + 4);
        for (int i = 0; i < len; i += 1) {
            char c = str.charAt(i);
            if (c >= 0x0100) {
                if (c < 0x1000) {
                    buf.append("\\u0").append(Integer.toString(c, 16));
                } else {
                    buf.append("\\u").append(Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    /**
     * Write a complete ArrayOf<ProgramElement>.
     */
    protected void writeImmutableArrayOfProgramElement(
            ImmutableArray<? extends ProgramElement> list) {
        int s = list.size();
        if (s == 0) {
            return;
        }
        list.get(0).visit(this);
        for (int i = 1; i < s; i += 1) {
            list.get(i).visit(this);
        }
    }

    /**
     * Write keyword list.
     *
     * @param list a program element list.
     */
    protected void writeKeywordList(ImmutableArray<Modifier> list) {
        for (int i = 0; i < list.size(); i++) {
            if (i != 0) {
                l.brk();
            }
            performActionOnModifier(list.get(i));
        }
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void writeCommaList(ImmutableArray<? extends ProgramElement> list) {
        for (int i = 0; i < list.size(); i++) {
            if (i != 0) {
                l.print(",").brk();
            }
            list.get(i).visit(this);
        }
    }

    protected void printOperator(Operator x, String symbol) {
        ImmutableArray<Expression> children = x.getArguments();
        if (children != null) {
            l.beginC();
            switch (x.getArity()) {
            case 2:
                children.get(0).visit(this);
                l.print(" ");
                l.print(symbol);
                l.brk();
                children.get(1).visit(this);
                break;
            case 1:
                switch (x.getNotation()) {
                case Operator.PREFIX:
                    l.print(symbol);
                    children.get(0).visit(this);
                    break;
                case Operator.POSTFIX:
                    children.get(0).visit(this);
                    l.print(symbol);
                    break;
                default:
                    break;
                }
            }
            l.end();
        }
    }

    private void printReferencePrefix(ReferencePrefix p) {
        if (p != null) {
            p.visit(this);
            l.print(".");
        }
    }

    private void printArguments(ImmutableArray<? extends Expression> args) {
        l.print("(");
        l.beginRelativeC(0);
        l.beginRelativeC().brk(0);
        if (args != null) {
            writeCommaList(args);
        }
        l.end();
        l.brk(0);
        l.end();
        l.print(")");
    }

    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
        String name = x.getProgramName();
        boolean isKey = (name.equals("int") || name.equals("float") || name.equals("char")
                || name.equals("short") || name.equals("long") || name.equals("boolean"));
        if (isKey) {
            l.markStartKeyword();
        }
        l.print(name);
        if (isKey) {
            l.markEndKeyword();
        }
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        l.print(x.name().toString());
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
        l.print(x.getMethodDeclaration().getProgramElementName().toString());
    }

    @Override
    public void performActionOnProgramMetaConstruct(ProgramTransformer x) {
        l.print(x.name().toString());
        l.print("(");
        if (x.getChildAt(0) != null) {
            x.getChildAt(0).visit(this);
        }
        l.print(")");
    }

    @Override
    public void performActionOnContextStatementBlock(ContextStatementBlock x) {
        if (x.getStatementCount() > 0) {
            l.print("{ .. ");
            writeImmutableArrayOfProgramElement(x.getBody());
            l.print(" ... }");
        } else {
            l.print("{ .. ");
            l.print(" ... }");
        }
    }

    @Override
    public void performActionOnIntLiteral(IntLiteral x) {
        l.print(x.getValueString());
    }

    @Override
    public void performActionOnBooleanLiteral(BooleanLiteral x) {
        l.keyWord(x.getValue() ? "true" : "false");
    }

    @Override
    public void performActionOnEmptySetLiteral(EmptySetLiteral x) {
        l.keyWord("\\empty");
    }

    private void printDLFunctionOperator(String name, Operator operator) {
        l.keyWord(name);
        if (operator.getArity() > 0) {
            printArguments(operator.getArguments());
        }
    }

    @Override
    public void performActionOnSingleton(de.uka.ilkd.key.java.expression.operator.adt.Singleton x) {
        printDLFunctionOperator("\\singleton", x);
    }

    @Override
    public void performActionOnSetUnion(de.uka.ilkd.key.java.expression.operator.adt.SetUnion x) {
        printDLFunctionOperator("\\set_union", x);
    }

    @Override
    public void performActionOnIntersect(Intersect x) {
        printDLFunctionOperator("\\intersect", x);
    }

    @Override
    public void performActionOnSetMinus(de.uka.ilkd.key.java.expression.operator.adt.SetMinus x) {
        printDLFunctionOperator("\\set_minus", x);
    }


    @Override
    public void performActionOnAllFields(de.uka.ilkd.key.java.expression.operator.adt.AllFields x) {
        printDLFunctionOperator("\\all_fields", x);
    }

    @Override
    public void performActionOnAllObjects(
            de.uka.ilkd.key.java.expression.operator.adt.AllObjects x) {
        printDLFunctionOperator("\\all_objects", x);
    }

    @Override
    public void performActionOnEmptySeqLiteral(EmptySeqLiteral x) {
        l.print("\\seq_empty");
    }

    @Override
    public void performActionOnSeqLength(SeqLength x) {
        x.getChildAt(0).visit(this);
        l.print(".length");
    }

    @Override
    public void performActionOnSeqGet(SeqGet x) {
        x.getChildAt(0).visit(this);
        l.print("[");
        x.getChildAt(1).visit(this);
        l.print("]");
    }

    @Override
    public void performActionOnSeqSingleton(
            de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton x) {
        printDLFunctionOperator("\\seq_singleton", x);
    }

    @Override
    public void performActionOnSeqConcat(de.uka.ilkd.key.java.expression.operator.adt.SeqConcat x) {
        printDLFunctionOperator("\\singleton", x);
    }

    @Override
    public void performActionOnSeqIndexOf(
            de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf x) {
        printDLFunctionOperator("\\indexOf", x);
    }

    @Override
    public void performActionOnSeqSub(de.uka.ilkd.key.java.expression.operator.adt.SeqSub x) {
        printDLFunctionOperator("\\seq_sub", x);
    }

    @Override
    public void performActionOnSeqReverse(
            de.uka.ilkd.key.java.expression.operator.adt.SeqReverse x) {
        printDLFunctionOperator("\\seq_reverse", x);
    }

    @Override
    public void performActionOnDLEmbeddedExpression(DLEmbeddedExpression x) {
        l.print("\\dl_" + x.getFunctionSymbol().name());
        l.print("(");

        for (int i = 0; i < x.getChildCount(); i++) {
            if (i != 0) {
                l.print(",").brk();
            }
            x.getChildAt(i).visit(this);
        }
        l.print(")");
    }

    @Override
    public void performActionOnStringLiteral(StringLiteral x) {
        l.print(encodeUnicodeChars(x.getValue()));
    }

    @Override
    public void performActionOnNullLiteral(NullLiteral x) {
        l.keyWord("null");
    }

    @Override
    public void performActionOnCharLiteral(CharLiteral x) {
        l.print(encodeUnicodeChars(x.toString()));
    }

    @Override
    public void performActionOnDoubleLiteral(DoubleLiteral x) {
        l.print(x.getValue());
    }

    @Override
    public void performActionOnMergePointStatement(MergePointStatement x) {
        // TODO syntax: @merge_point like @assert?
        l.print("//@ merge_point (");
        l.print(x.getExpression().toString());
        l.print(");");
    }

    @Override
    public void performActionOnLongLiteral(LongLiteral x) {
        l.print(x.getValueString());
    }

    @Override
    public void performActionOnFloatLiteral(FloatLiteral x) {
        l.print(x.getValue());
    }

    @Override
    public void performActionOnPackageSpecification(PackageSpecification x) {
        l.nl();
        l.keyWord("package");
        l.print(" ");
        performActionOnPackageReference(x.getPackageReference());
        l.print(";");
    }

    @Override
    public void performActionOnAssert(Assert x) {
        l.keyWord("assert");
        l.print(" ");

        x.getCondition().visit(this);

        if (x.getMessage() != null) {
            l.print(" :");
            l.brk();
            x.getMessage().visit(this);
        }
    }

    public void performActionOnJavaProgramElement(JavaProgramElement element) {
        Comment[] comments = element.getComments();
        int s = (comments != null) ? comments.length : 0;
        int t = 0;
        for (int i = 0; i < s; i += 1) {
            Comment c = comments[i];
            if (c.isPrefixed()) {
                performActionOnComment(c);
            } else {
                t += 1;
            }
        }
        if (t > 0) {
            for (int i = 0; i < s; i += 1) {
                Comment c = comments[i];
                if (!c.isPrefixed()) {
                    if (c instanceof SingleLineComment) {
                        // TODO ignored by current pretty printer
                        // scheduleComment((SingleLineComment) c);
                    } else {
                        performActionOnComment(c);
                    }
                }
            }
        }
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant constant) {
        performActionOnProgramVariable(constant);
    }

    @Override
    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
        if (!(x instanceof SchemaTypeReference)) {
            throw new UnsupportedOperationException();
        }
        performActionOnSchemaTypeReference((SchemaTypeReference) x);
    }

    @Override
    public void performActionOnIProgramVariable(IProgramVariable x) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x) {
        performActionOnJavaProgramElement(x);
    }

    @Override
    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
        performActionOnVariableDeclaration(x);
    }

    @Override
    public void performActionOnFieldSpecification(FieldSpecification x) {
        performActionOnVariableSpecification(x);
    }

    @Override
    public void performActionOnImplicitFieldSpecification(ImplicitFieldSpecification x) {
        performActionOnVariableSpecification(x);
    }

    @Override
    public void performActionOnSchematicFieldReference(SchematicFieldReference x) {
        performActionOnFieldReference(x);
    }

    @Override
    public void performActionOnVariableReference(VariableReference x) {
        performActionOnProgramVariable(x.getProgramVariable());
    }

    @Override
    public void performActionOnConstructorDeclaration(ConstructorDeclaration x) {
        performActionOnMethodDeclaration(x);
    }

    @Override
    public void performActionOnForUpdates(ForUpdates x) {
        // TODO
        performActionOnJavaProgramElement(x);
    }

    @Override
    public void performActionOnGuard(Guard x) {
        // TODO
        performActionOnJavaProgramElement(x);
    }

    @Override
    public void performActionOnLoopInit(LoopInit x) {
        performActionOnJavaProgramElement(x);
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable variable) {
        performActionOnProgramVariable(variable);
    }

    @Override
    public void performActionOnLoopInvariant(LoopSpecification x) {
        // TODO
    }

    @Override
    public void performActionOnBlockContract(BlockContract x) {
        // TODO
    }

    @Override
    public void performActionOnLoopContract(LoopContract x) {
        // TODO
    }

    @Override
    public void performActionOnBlockContract(StatementBlock oldBlock, StatementBlock newBlock) {
        // TODO
    }

    @Override
    public void performActionOnLoopContract(StatementBlock oldBlock, StatementBlock newBlock) {
        // TODO
    }

    @Override
    public void performActionOnLoopContract(LoopStatement oldLoop, LoopStatement newLoop) {
        // TODO
    }

    @Override
    public void performActionOnMergeContract(MergeContract x) {
        // TODO
    }

    @Override
    public void performActionOnJmlAssertCondition(Term cond) {
        // TODO
    }

    @Override
    public void performActionOnArrayDeclaration(ArrayDeclaration type) {
        Type baseType = type.getBaseType().getKeYJavaType().getJavaType();
        assert baseType != null;
        if (baseType instanceof ArrayDeclaration) {
            performActionOnArrayDeclaration((ArrayDeclaration) baseType);
        } else {
            l.print(baseType.getFullName());
        }
        l.print("[]");
    }

    @Override
    public void performActionOnTypeReference(TypeReference x) {
        performActionOnTypeReference(x, false);
    }

    public void performActionOnTypeReference(TypeReference x, boolean fullTypeNames) {
        if (x.getKeYJavaType() != null
                && x.getKeYJavaType().getJavaType() instanceof ArrayDeclaration) {
            performActionOnArrayDeclaration((ArrayDeclaration) x.getKeYJavaType().getJavaType());
        } else if (x.getProgramElementName() != null) {
            printTypeReference(x.getReferencePrefix(), x.getKeYJavaType(),
                x.getProgramElementName(), fullTypeNames);
        }
    }

    private void printTypeReference(ReferencePrefix prefix, KeYJavaType type,
            ProgramElementName name, boolean fullTypeNames) {
        printReferencePrefix(prefix);
        if (fullTypeNames) {
            l.print(type.getFullName());
        } else {
            performActionOnProgramElementName(name);
        }
    }

    public void performActionOnSchemaTypeReference(SchemaTypeReference x) {
        performActionOnTypeReference(x, false);
    }

    @Override
    public void performActionOnFieldReference(FieldReference x) {
        if (x.getName() != null
                && "javax.realtime.MemoryArea::currentMemoryArea".equals(x.getName())) {
            l.print("<currentMemoryArea>");
        } else {
            printTypeReference(x.getReferencePrefix(), x.getKeYJavaType(),
                x.getProgramElementName(), false);
        }
    }

    @Override
    public void performActionOnPackageReference(PackageReference x) {
        printTypeReference(x.getReferencePrefix(), null, x.getProgramElementName(), false);
    }

    @Override
    public void performActionOnThrows(Throws x) {
        if (x.getExceptions() != null) {
            l.keyWord("throws").print(" ");

            writeCommaList(x.getExceptions());
        }
    }

    @Override
    public void performActionOnArrayInitializer(ArrayInitializer x) {
        l.print("{");
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        l.print("}");
    }

    @Override
    public void performActionOnCompilationUnit(CompilationUnit x) {
        // TODO
        throw new UnsupportedOperationException();
        // boolean hasPackageSpec = (x.getPackageSpecification() != null);
        // if (hasPackageSpec) {
        // performActionOnPackageSpecification(x.getPackageSpecification());
        // }
        // boolean hasImports = (x.getImports() != null) && (x.getImports().size() > 0);
        // if (hasImports) {
        // writeLineList((x.getPackageSpecification() != null) ? 2 : 0, 0, x.getImports());
        // }
        // if (x.getDeclarations() != null) {
        // writeBlockList((hasImports || hasPackageSpec) ? 2 : 0, 0, x.getDeclarations());
        // }
    }

    @Override
    public void performActionOnClassDeclaration(ClassDeclaration x) {
        // TODO
        throw new UnsupportedOperationException();
        // int m = 0;
        // if (x.getModifiers() != null) {
        // m = x.getModifiers().size();
        // }
        // if (m > 0) {
        // ImmutableArray<Modifier> mods = x.getModifiers();
        // writeKeywordList(mods);
        // m = 1;
        // }
        // if (x.getProgramElementName() != null) {
        // l.keyWord("class");
        // writeElement(1, x.getProgramElementName());
        // }
        // if (x.getExtendedTypes() != null) {
        // writeElement(1, x.getExtendedTypes());
        // }
        // if (x.getImplementedTypes() != null) {
        // writeElement(1, x.getImplementedTypes());
        // }
        // if (x.getProgramElementName() != null) {
        // l.print(" {");
        // } else { // anonymous class
        // l.print("{");
        // }
        // if (x.getMembers() != null) {
        // // services.getJavaInfo().getKeYProgModelInfo().getConstructors(kjt)
        // writeBlockList(2, 1, x.getMembers());
        // }
        // l.print("}");
    }

    @Override
    public void performActionOnInterfaceDeclaration(InterfaceDeclaration x) {
        // TODO
        throw new UnsupportedOperationException();
        // int m = 0;
        // if (x.getModifiers() != null) {
        // m = x.getModifiers().size();
        // }
        // if (m > 0) {
        // writeKeywordList(x.getModifiers());
        // m = 1;
        // }
        // if (x.getProgramElementName() != null) {
        // l.keyWord("interface");
        // writeElement(1, x.getProgramElementName());
        // }
        // if (x.getExtendedTypes() != null) {
        // writeElement(1, x.getExtendedTypes());
        // }
        // l.print(" {");
        // if (x.getMembers() != null) {
        // writeBlockList(2, 1, x.getMembers());
        // }
        // l.print("}");
    }

    @Override
    public void performActionOnFieldDeclaration(FieldDeclaration x) {
        performActionOnVariableDeclaration(x);
    }

    @Override
    public void performActionOnLocalVariableDeclaration(LocalVariableDeclaration x) {
        performActionOnVariableDeclaration(x);
    }

    @Override
    public void performActionOnVariableDeclaration(VariableDeclaration x) {
        l.beginI();
        ImmutableArray<Modifier> modifiers = x.getModifiers();
        if (modifiers != null && !modifiers.isEmpty()) {
            writeKeywordList(modifiers);
            l.print(" ");
        }
        performActionOnTypeReference(x.getTypeReference());
        l.print(" ");
        ImmutableArray<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            writeCommaList(varSpecs);
        }
        l.end();
    }

    @Override
    public void performActionOnMethodDeclaration(MethodDeclaration x) {
        throw new UnsupportedOperationException();
        // Comment[] c = x.getComments();
        // int m = c.length;
        // for (Comment aC : c) {
        // performActionOnComment(aC);
        // }
        // if (x.getModifiers() != null) {
        // ImmutableArray<Modifier> mods = x.getModifiers();
        // m += mods.size();
        // writeKeywordList(mods);
        // }
        // if (x.getTypeReference() != null) {
        // if (m > 0) {
        // writeElement(1, x.getTypeReference());
        // } else {
        // performActionOnTypeReference(x.getTypeReference());
        // }
        // writeElement(1, x.getProgramElementName());
        // } else if (x.getTypeReference() == null && !(x instanceof ConstructorDeclaration)) {
        // l.print(" void ");
        // writeElement(1, x.getProgramElementName());
        // } else {
        // if (m > 0) {
        // writeElement(1, x.getProgramElementName());
        // } else {
        // performActionOnProgramElementName(x.getProgramElementName());
        // }
        // }
        // l.print(" (");
        // if (x.getParameters() != null) {
        // writeCommaList(x.getParameters());
        // }
        // l.print(")");
        // if (x.getThrown() != null) {
        // writeElement(1, x.getThrown());
        // }
        // if (x.getBody() != null) {
        // writeElement(1, x.getBody());
        // } else {
        // l.print(";");
        // }
    }

    @Override
    public void performActionOnClassInitializer(ClassInitializer x) {
        l.beginC();
        if (x.getModifiers() != null) {
            writeKeywordList(x.getModifiers());
            l.print(" ");
        }
        l.end();
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    public void performActionOnStatement(Statement statement) {
        l.beginC(0);
        boolean validStatement = !(statement instanceof CatchAllStatement || statement instanceof ProgramPrefix);
        if (validStatement) {
            markStart(statement);
        }
        statement.visit(this);
        if (validStatement) {
            markEnd(statement);
        }
        if (!(statement instanceof BranchStatement) && !(statement instanceof StatementContainer)) {
            l.print(";");
        }
        l.end();
    }

    @Override
    public void performActionOnStatementBlock(StatementBlock x) {
        l.beginC(0);
        printStatementBlock(x);
        l.end();
    }

    public boolean printStatementBlock(StatementBlock x) {
        boolean emptyBlock = x.getBody() == null || x.getBody().isEmpty();
        if (emptyBlock) {
            // We have an empty statement block ...
            markStart(x);
            l.print("{}");
            markEnd(x);
            return false;
        } else {
            l.print("{");
            l.beginRelativeC();
            for (Statement statement : x.getBody()) {
                l.nl();
                performActionOnStatement(statement);
            }
            l.end().nl().print("}");
            return true;
        }
    }

    @Override
    public void performActionOnBreak(Break x) {
        l.keyWord("break");
        if (x.getProgramElementName() != null) {
            l.brk();
            performActionOnProgramElementName(x.getProgramElementName());
        }
    }

    @Override
    public void performActionOnContinue(Continue x) {
        l.keyWord("continue");
        if (x.getProgramElementName() != null) {
            l.brk();
            performActionOnProgramElementName(x.getProgramElementName());
        }
    }

    @Override
    public void performActionOnReturn(Return x) {
        l.keyWord("return");
        if (x.getExpression() != null) {
            l.brk();
            x.getExpression().visit(this);
        }
    }

    @Override
    public void performActionOnThrow(Throw x) {
        l.keyWord("throw");
        if (x.getExpression() != null) {
            l.brk();
            x.getExpression().visit(this);
        }
    }

    @Override
    public void performActionOnDo(Do x) {
        performActionOnDo(x, true);
    }

    private boolean handleBlockOrSingleStatement(Statement body) {
        if (body instanceof StatementBlock) {
            l.print(" ");
            return printStatementBlock((StatementBlock) body);
        } else {
            l.beginRelativeC();
            l.brk();
            body.visit(this);
            l.print(";");
            l.end();
            return false;
        }
    }

    private boolean handleBlockStatementOrEmpty(Statement body, boolean includeBody) {
        if (includeBody) {
            if (body == null || body instanceof EmptyStatement) {
                l.print(";");
                return false;
            } else {
                return handleBlockOrSingleStatement(body);
            }
        } else {
            l.print(" ... ");
            return false;
        }
    }

    public void performActionOnDo(Do x, boolean includeBody) {
        l.keyWord("do");

        boolean newBlock = handleBlockStatementOrEmpty(x.getBody(), includeBody);
        handleContinuationAfterNewBlock(newBlock);

        l.keyWord("while");
        l.print(" (");
        l.beginC();
        if (x.getGuardExpression() != null) {
            x.getGuardExpression().visit(this);
        }
        l.print(");").end();
    }

    @Override
    public void performActionOnEnhancedFor(EnhancedFor x) {
        performActionOnEnhancedFor(x, true);
    }

    public void performActionOnEnhancedFor(EnhancedFor x, boolean includeBody) {
        l.beginC();
        l.keyWord("for");
        l.print(" (");
        l.beginC(0);

        ImmutableArray<LoopInitializer> initializers = x.getInitializers();
        if (initializers != null) {
            initializers.get(0).visit(this);
        }

        l.print(" :");
        l.brk();

        if (x.getGuard() != null) {
            x.getGuardExpression().visit(this);
        }

        l.print(")");
        l.end();

        handleBlockStatementOrEmpty(x.getBody(), includeBody);
        l.end();
    }

    @Override
    public void performActionOnFor(For x) {
        performActionOnFor(x, true);
    }

    public void performActionOnFor(For x, boolean includeBody) {
        l.keyWord("for");
        l.print(" (");
        l.beginC();

        // there is no "getLoopInit" method
        // so get the first child of the for loop
        ILoopInit init = x.getILoopInit();
        if (init != null) {
            if (init instanceof ProgramSV) {
                init.visit(this);
            } else {
                writeCommaList(x.getInitializers());
            }
        }
        l.print(";").brk();
        if (x.getGuardExpression() != null) {
            x.getGuardExpression().visit(this);
        }
        l.print(";").brk();

        IForUpdates upd = x.getIForUpdates();
        if (upd != null) {
            if (upd instanceof ProgramSV) {
                upd.visit(this);
            } else {
                writeCommaList(x.getUpdates());
            }
        }
        l.print(")");
        l.end();

        handleBlockStatementOrEmpty(x.getBody(), includeBody);
    }

    @Override
    public void performActionOnWhile(While x) {
        performActionOnWhile(x, true);
    }

    public void performActionOnWhile(While x, boolean includeBody) {
        l.keyWord("while");
        l.print(" (");
        l.beginC();
        if (x.getGuardExpression() != null) {
            x.getGuardExpression().visit(this);
        }
        l.end();
        l.print(")");

        handleBlockStatementOrEmpty(x.getBody(), includeBody);
    }

    @Override
    public void performActionOnIf(If x) {
        performActionOnIf(x, true);
    }

    private void handleContinuationAfterNewBlock(boolean newBlock) {
        if (newBlock) {
            l.print(" ");
        } else {
            l.nl();
        }
    }

    public void performActionOnIf(If x, boolean includeBranches) {
        l.keyWord("if");
        l.print(" (");
        l.beginRelativeC();
        if (x.getExpression() != null) {
            x.getExpression().visit(this);
        }
        l.end();
        l.print(")");

        if (includeBranches) {
            boolean newBlock = handleBlockOrSingleStatement(x.getThen().getBody());
            if (x.getElse() != null) {
                handleContinuationAfterNewBlock(newBlock);
            }
            Else e = x.getElse();
            if (x.getElse() != null) {
                performActionOnElse(e);
            }
        }
    }

    @Override
    public void performActionOnSwitch(Switch x) {
        performActionOnSwitch(x, true);
    }

    public void performActionOnSwitch(Switch x, boolean includeBranches) {
        // TODO
        l.keyWord("switch");
        l.print(" (");
        if (x.getExpression() != null) {
            x.getExpression().visit(this);
        }
        l.print(")");
        if (includeBranches) {
            l.print(" {");
            if (x.getBranchList() != null) {
                writeImmutableArrayOfProgramElement(x.getBranchList());
            }
            l.print("}");
        }
    }

    private void printTryLike(String name, StatementBlock body, ImmutableArray<Branch> branches) {
        l.keyWord(name);
        l.print(" ");
        if (body != null) {
            printStatementBlock(body);
        }
        if (branches != null) {
            for (Branch branch : branches) {
                branch.visit(this);
            }
        }
    }

    @Override
    public void performActionOnTry(Try x) {
        printTryLike("try", x.getBody(), x.getBranchList());
    }

    @Override
    public void performActionOnLabeledStatement(LabeledStatement x) {
        if (x.getLabel() != null) {
            x.getLabel().visit(this);
            l.print(":").nl();
        }

        if (x.getBody() != null) {
            x.getBody().visit(this);
        }
    }

    @Override
    public void performActionOnMethodFrame(MethodFrame x) {
        l.keyWord("method-frame");
        l.print(" (");
        l.beginRelativeC(0);
        l.beginRelativeC().brk(0);
        IProgramVariable var = x.getProgramVariable();
        if (var != null) {
            l.beginRelativeC().print("result ->").brk();
            var.visit(this);
            l.print(",").end().brk();
        }

        if (x.getExecutionContext() instanceof ExecutionContext) {
            performActionOnExecutionContext((ExecutionContext) x.getExecutionContext());
        } else {
            performActionOnSchemaVariable((SchemaVariable) x.getExecutionContext());
        }

        l.end().brk(0).end();
        l.print(") ");
        // TODO is this needed?
        // l.print(": ");

        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnCatchAllStatement(CatchAllStatement x) {
        // TODO
        l.print("#catchAll");
        l.print("(");
        performActionOnLocationVariable(x.getParam());
        l.print(")");
        x.getBody().visit(this);
    }

    @Override
    public void performActionOnMethodBodyStatement(MethodBodyStatement x) {
        IProgramVariable pvar = x.getResultVariable();
        if (pvar != null) {
            pvar.visit(this);
            l.brk(1, 0);
            l.print("=");
            l.brk(1, 0);
        }

        printMethodReference(x.getMethodReference());
        // CHG:
        l.print("@");
        final TypeReference tr = x.getBodySourceAsTypeReference();
        if (tr instanceof SchemaTypeReference) {
            performActionOnSchemaTypeReference((SchemaTypeReference) tr);
        } else if (tr instanceof SchemaVariable) {
            performActionOnSchemaVariable((SchemaVariable) tr);
        } else {
            performActionOnTypeReference(tr);
        }
    }

    @Override
    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
        l.print("synchronized");
        if (x.getExpression() != null) {
            l.beginC();
            l.print(" (");
            x.getExpression().visit(this);
            l.print(")");
            l.end();
        }
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnLoopScopeBlock(LoopScopeBlock x) {
        l.keyWord("loop-scope");
        l.print(" (");
        l.beginRelativeC(0).brk(0);
        l.beginRelativeC();
        if (x.getIndexPV() != null) {
            x.getIndexPV().visit(this);
        }
        l.end().brk(0).end();
        l.print(") ");
        printStatementBlock(x.getBody());
    }

    @Override
    public void performActionOnImport(Import x) {
        l.print("import ");
        x.getReference().visit(this);
        if (x.isMultiImport()) {
            l.print(".*;");
        } else {
            l.print(";");
        }
    }

    @Override
    public void performActionOnExtends(Extends x) {
        if (x.getSupertypes() != null) {
            l.keyWord("extends");
            writeCommaList(x.getSupertypes());
        }
    }

    @Override
    public void performActionOnImplements(Implements x) {
        if (x.getSupertypes() != null) {
            l.keyWord("implements");
            l.print(" ");
            writeCommaList(x.getSupertypes());
        }
    }

    @Override
    public void performActionOnVariableSpecification(VariableSpecification x) {
        x.getProgramVariable().visit(this);
        for (int i = 0; i < x.getDimensions(); i += 1) {
            l.print("[]");
        }
        if (x.getInitializer() != null) {
            l.print(" = ");
            x.getInitializer().visit(this);
        }
    }

    @Override
    public void performActionOnBinaryAnd(BinaryAnd x) {
        printOperator(x, "&");
    }

    @Override
    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
        printOperator(x, "&=");
    }

    @Override
    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
        printOperator(x, "|=");
    }

    @Override
    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
        printOperator(x, "^=");
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
        x.getArguments().get(0).visit(this);
        l.print(" = ");
        x.getArguments().get(1).visit(this);
    }

    @Override
    public void performActionOnDivideAssignment(DivideAssignment x) {
        printOperator(x, "/=");
    }

    @Override
    public void performActionOnMinusAssignment(MinusAssignment x) {
        printOperator(x, "-=");
    }

    @Override
    public void performActionOnModuloAssignment(ModuloAssignment x) {
        printOperator(x, "%=");
    }

    @Override
    public void performActionOnPlusAssignment(PlusAssignment x) {
        printOperator(x, "+=");
    }

    @Override
    public void performActionOnPostDecrement(PostDecrement x) {
        printOperator(x, "--");
    }

    @Override
    public void performActionOnPostIncrement(PostIncrement x) {
        printOperator(x, "++");
    }

    @Override
    public void performActionOnPreDecrement(PreDecrement x) {
        printOperator(x, "--");
    }

    @Override
    public void performActionOnPreIncrement(PreIncrement x) {
        printOperator(x, "++");
    }

    @Override
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
        printOperator(x, "<<=");
    }

    @Override
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
        printOperator(x, ">>=");
    }

    @Override
    public void performActionOnTimesAssignment(TimesAssignment x) {
        printOperator(x, "*=");
    }

    @Override
    public void performActionOnUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {
        printOperator(x, ">>>=");
    }

    @Override
    public void performActionOnBinaryNot(BinaryNot x) {
        printOperator(x, "~");
    }

    @Override
    public void performActionOnBinaryOr(BinaryOr x) {
        printOperator(x, "|");
    }

    @Override
    public void performActionOnBinaryXOr(BinaryXOr x) {
        printOperator(x, "^");
    }

    @Override
    public void performActionOnConditional(Conditional x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (x.getArguments() != null) {
            l.beginC();
            if (addParentheses) {
                l.print("(");
            }
            x.getArguments().get(0).visit(this);
            l.print(" ?").brk();
            x.getArguments().get(1).visit(this);
            l.print(" :").brk();
            x.getArguments().get(2).visit(this);
            if (addParentheses) {
                l.print(")");
            }
            l.end();
        }
    }

    @Override
    public void performActionOnDivide(Divide x) {
        printOperator(x, "/");
    }

    @Override
    public void performActionOnEquals(Equals x) {
        printOperator(x, "==");
    }

    @Override
    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
        printOperator(x, ">=");
    }

    @Override
    public void performActionOnGreaterThan(GreaterThan x) {
        printOperator(x, ">");
    }

    @Override
    public void performActionOnLessOrEquals(LessOrEquals x) {
        printOperator(x, "<=");
    }

    @Override
    public void performActionOnLessThan(LessThan x) {
        printOperator(x, "<");
    }

    @Override
    public void performActionOnNotEquals(NotEquals x) {
        printOperator(x, "!=");
    }

    @Override
    public void performActionOnNewArray(NewArray x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            l.print("(");
        }
        l.print("new ");

        performActionOnTypeReference(x.getTypeReference());
        int i = 0;
        if (x.getArguments() != null) {
            for (; i < x.getArguments().size(); i += 1) {
                l.print("[");
                x.getArguments().get(i).visit(this);
                l.print("]");
            }
        }
        for (; i < x.getDimensions(); i += 1) {
            l.print("[]");
        }
        if (x.getArrayInitializer() != null) {
            performActionOnArrayInitializer(x.getArrayInitializer());
        }
        if (addParentheses) {
            l.print(")");
        }
    }

    private void printInstanceOfLike(TypeOperator op, String kw) {
        boolean addParentheses = op.isToBeParenthesized();
        if (addParentheses) {
            l.print("(");
        }
        if (op.getArguments() != null) {
            op.getExpressionAt(0).visit(this);
        }
        l.print(" ");
        l.keyWord(kw);
        l.brk();
        if (op.getTypeReference() != null) {
            performActionOnTypeReference(op.getTypeReference());
        }
        if (addParentheses) {
            l.print(")");
        }
    }

    @Override
    public void performActionOnInstanceof(Instanceof x) {
        printInstanceOfLike(x, "instanceof");
    }


    @Override
    public void performActionOnExactInstanceof(ExactInstanceof x) {
        printInstanceOfLike(x, "exactInstanceof");
    }

    @Override
    public void performActionOnNew(New x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            l.print("(");
        }
        printReferencePrefix(x.getReferencePrefix());
        l.keyWord("new").print(" ");

        performActionOnTypeReference(x.getTypeReference());
        printArguments(x.getArguments());
        if (x.getClassDeclaration() != null) {
            performActionOnClassDeclaration(x.getClassDeclaration());
        }
        if (addParentheses) {
            l.print(")");
        }
    }

    @Override
    public void performActionOnTypeCast(TypeCast x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            l.print("(");
        }
        l.print("(");
        if (x.getTypeReference() != null) {
            performActionOnTypeReference(x.getTypeReference());
        }
        l.print(") ");
        if (x.getArguments() != null) {
            x.getArguments().get(0).visit(this);
        }
        if (addParentheses) {
            l.print(")");
        }
    }

    @Override
    public void performActionOnLogicalAnd(LogicalAnd x) {
        printOperator(x, "&&");
    }

    @Override
    public void performActionOnLogicalNot(LogicalNot x) {
        printOperator(x, "!");
    }

    @Override
    public void performActionOnLogicalOr(LogicalOr x) {
        printOperator(x, "||");
    }

    @Override
    public void performActionOnMinus(Minus x) {
        printOperator(x, "-");
    }

    @Override
    public void performActionOnModulo(Modulo x) {
        printOperator(x, "%");
    }

    @Override
    public void performActionOnNegative(Negative x) {
        printOperator(x, "-");
    }

    @Override
    public void performActionOnPlus(Plus x) {
        printOperator(x, "+");
    }

    @Override
    public void performActionOnPositive(Positive x) {
        printOperator(x, "+");
    }

    @Override
    public void performActionOnShiftLeft(ShiftLeft x) {
        printOperator(x, "<<");
    }

    @Override
    public void performActionOnShiftRight(ShiftRight x) {
        printOperator(x, ">>");
    }

    @Override
    public void performActionOnTimes(Times x) {
        printOperator(x, "*");
    }

    @Override
    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x) {
        printOperator(x, ">>>");
    }

    @Override
    public void performActionOnArrayReference(ArrayReference x) {
        x.getReferencePrefix().visit(this);
        int s = x.getDimensionExpressions().size();
        for (int i = 0; i < s; i += 1) {
            l.print("[");
            x.getDimensionExpressions().get(i).visit(this);
            l.print("]");
        }
    }

    @Override
    public void performActionOnMetaClassReference(MetaClassReference x) {
        if (x.getTypeReference() != null) {
            performActionOnTypeReference(x.getTypeReference());
            l.print(".");
        }
        l.print("class");
    }

    @Override
    public void performActionOnMethodReference(MethodReference x) {
        printMethodReference(x);
    }

    protected void printMethodReference(MethodReference x) {
        printReferencePrefix(x.getReferencePrefix());
        if (x.getProgramElementName() != null) {
            x.getMethodName().visit(this);
        }

        printArguments(x.getArguments());
    }

    @Override
    public void performActionOnMethod(IProgramMethod x) {
        l.print(x.name().toString());
    }

    protected void writeFullMethodSignature(IProgramMethod x) {
        l.print(x.getName());
        l.print("(");
        boolean afterFirst = false;
        for (ParameterDeclaration pd : x.getParameters()) {
            if (afterFirst) {
                l.print(", ");
            } else {
                afterFirst = true;
            }
            performActionOnTypeReference(pd.getTypeReference(), true);
        }
        l.print(")");
    }

    @Override
    public void performActionOnExecutionContext(ExecutionContext x) {
        l.beginRelativeC(0);
        l.beginRelativeC();
        l.print("source =").brk();
        writeFullMethodSignature(x.getMethodContext());
        l.print("@");
        performActionOnTypeReference(x.getTypeReference());
        if (x.getRuntimeInstance() != null) {
            l.print(",").end().brk().beginRelativeC().print("this =").brk();
            x.getRuntimeInstance().visit(this);
            l.end();
        } else {
            l.end();
        }
        l.end();
    }

    @Override
    public void performActionOnSuperConstructorReference(SuperConstructorReference x) {
        printReferencePrefix(x.getReferencePrefix());
        l.keyWord("super");
        printArguments(x.getArguments());
    }

    @Override
    public void performActionOnThisConstructorReference(ThisConstructorReference x) {
        l.keyWord("this");
        printArguments(x.getArguments());
    }

    @Override
    public void performActionOnSuperReference(SuperReference x) {
        printReferencePrefix(x.getReferencePrefix());
        l.keyWord("super");
    }

    @Override
    public void performActionOnThisReference(ThisReference x) {
        printReferencePrefix(x.getReferencePrefix());
        l.keyWord("this");
    }

    @Override
    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
        printReferencePrefix(x.getReferencePrefix());
        l.print("length");
    }

    @Override
    public void performActionOnThen(Then x) {
        throw new IllegalStateException("Shouldn't get here");
    }

    @Override
    public void performActionOnElse(Else x) {
        l.keyWord("else");
        Statement body = x.getBody();
        if (body instanceof If) {
            l.print(" ");
            performActionOnIf((If) body);
        } else {
            handleBlockOrSingleStatement(body);
        }
    }

    @Override
    public void performActionOnCase(Case x) {
        // TODO
        l.keyWord("case");
        l.print(" ");
        if (x.getExpression() != null) {
            x.getExpression().visit(this);
        }
        l.print(":");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeImmutableArrayOfProgramElement(x.getBody());
        }
    }

    @Override
    public void performActionOnCatch(Catch x) {
        l.print(" ");
        l.keyWord("catch");
        l.print(" (");
        l.beginC();
        if (x.getParameterDeclaration() != null) {
            performActionOnParameterDeclaration(x.getParameterDeclaration());
        }
        l.end();
        l.print(") ");
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnDefault(Default x) {
        // TODO
        l.keyWord("default").print(":");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeImmutableArrayOfProgramElement(x.getBody());
        }
    }

    @Override
    public void performActionOnFinally(Finally x) {
        l.print(" ");
        l.keyWord("finally");
        l.print(" ");
        if (x.getBody() != null) {
            performActionOnStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnModifier(Modifier x) {
        l.keyWord(x.getText());
    }

    @SuppressWarnings("unchecked")
    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        if (!(x instanceof ProgramSV)) {
            throw new UnsupportedOperationException(
                "Don't know how to pretty print non program SV in programs.");
        }

        Object o = instantiations.getInstantiation(x);
        if (o == null) {
            l.print(x.name().toString());
        } else {
            if (o instanceof ProgramElement) {
                ((ProgramElement) o).visit(this);
            } else if (o instanceof ImmutableArray) {
                // TODO what even is this
                writeImmutableArrayOfProgramElement((ImmutableArray<ProgramElement>) o);
            } else {
                LOGGER.warn("No PrettyPrinting available for {}", o.getClass().getName());
            }
        }
    }

    @Override
    public void performActionOnEmptyStatement(EmptyStatement x) {}

    @Override
    public void performActionOnComment(Comment x) {
        l.print("/* " + x.getText().trim() + " */");
    }

    @Override
    public void performActionOnParenthesizedExpression(ParenthesizedExpression x) {
        l.print("(");
        if (x.getArguments() != null) {
            x.getArguments().get(0).visit(this);
        }
        l.print(")");
    }

    @Override
    public void performActionOnPassiveExpression(PassiveExpression x) {
        l.print("@(");
        if (x.getArguments() != null) {
            x.getArguments().get(0).visit(this);
        }
        l.print(")");
    }

    @Override
    public void performActionOnTransactionStatement(TransactionStatement x) {
        l.print(x.toString());
    }

    @Override
    public void performActionOnEmptyMapLiteral(EmptyMapLiteral x) {
        l.print("\\map_empty");
    }

    @Override
    public void performActionOnExec(Exec x) {
        // TODO what is this?
        printTryLike("exec", x.getBody(), x.getBranchList());
    }

    @Override
    public void performActionOnCcatch(Ccatch x) {
        l.print(" ");
        l.keyWord("ccatch");
        l.print(" (");
        if (x.hasParameterDeclaration()) {
            performActionOnParameterDeclaration(x.getParameterDeclaration());
        } else if (x.hasNonStdParameterDeclaration()) {
            x.getNonStdParameterDeclaration().visit(this);
        }
        l.print(") ");
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnCcatchReturnParameterDeclaration(
            CcatchReturnParameterDeclaration x) {
        l.keyWord("\\Return");
    }

    @Override
    public void performActionOnCcatchReturnValParameterDeclaration(
            CcatchReturnValParameterDeclaration x) {
        l.keyWord("\\Return");
        l.print(" ");
        x.getDelegate().visit(this);
    }

    @Override
    public void performActionOnCcatchContinueParameterDeclaration(
            CcatchContinueParameterDeclaration x) {
        l.keyWord("\\Continue");
    }

    @Override
    public void performActionOnCcatchBreakParameterDeclaration(CcatchBreakParameterDeclaration x) {
        l.keyWord("\\Break");
    }

    @Override
    public void performActionOnCcatchBreakLabelParameterDeclaration(
            CcatchBreakLabelParameterDeclaration x) {
        l.keyWord("\\Break");
        l.print(" ");
        if (x.getLabel() != null) {
            x.getLabel().visit(this);
        }
    }

    @Override
    public void performActionOnCCcatchContinueLabelParameterDeclaration(
            CcatchContinueLabelParameterDeclaration x) {
        l.keyWord("\\Continue");
        l.print(" ");
        if (x.getLabel() != null) {
            x.getLabel().visit(this);
        }
    }

    @Override
    public void performActionOnCcatchBreakWildcardParameterDeclaration(
            CcatchBreakWildcardParameterDeclaration x) {
        l.keyWord("\\Break");
        l.print(" *");
    }

    @Override
    public void performActionOnCcatchContinueWildcardParameterDeclaration(
            CcatchContinueWildcardParameterDeclaration x) {
        l.keyWord("\\Continue");
    }

    /**
     * Prints the JML assert statement.
     *
     * @param jmlAssert the statement to print
     */
    @Override
    public void performActionOnJmlAssert(JmlAssert jmlAssert) {
        l.markStartKeyword();
        l.print("@");
        final String kind = jmlAssert.getKind().name().toLowerCase();
        l.print(kind);
        l.markEndKeyword();
        l.brk();

        l.print(jmlAssert.getConditionText().trim());
    }
}
