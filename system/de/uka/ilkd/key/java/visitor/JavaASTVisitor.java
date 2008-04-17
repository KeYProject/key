// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.visitor;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.*;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramMetaConstruct;
import de.uka.ilkd.key.rule.soundness.ProgramSVProxy;
import de.uka.ilkd.key.rule.soundness.ProgramSVSkolem;
import de.uka.ilkd.key.speclang.LoopInvariant;

/** 
 * Extends the JavaASTWalker to use the visitor mechanism. The
 * methods inherited by the Visitor interface are all implemented that
 * they call the method <code> doDefaultAction(ProgramElement) </code>.
 */
public abstract class JavaASTVisitor extends JavaASTWalker 
    implements Visitor {
    
    protected final Services services;
    

    /** create the JavaASTVisitor
     * @param root the ProgramElement where to begin
     * @param services the Services object
     */
    public JavaASTVisitor(ProgramElement root, Services services) {
	super(root);
        this.services = services;
    }
    
    
    protected void walk(ProgramElement node) {
        super.walk(node);
        if(node instanceof LoopStatement && services != null) {
            LoopInvariant li = services.getSpecificationRepository()
                                       .getLoopInvariant((LoopStatement) node);
            if(li != null) {
                performActionOnLoopInvariant(li);
            }
        }
    }
    
    
    /**
     * the action that is performed just before leaving the node the last time
     */
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }
    

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected abstract void doDefaultAction(SourceElement node) ;

    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
	doDefaultAction(x);
    }

    public void performActionOnArrayDeclaration(ArrayDeclaration x) {
	doDefaultAction(x);
    }
    
    public void performActionOnArrayInitializer(ArrayInitializer x) {
	doDefaultAction(x);
    }

    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
	doDefaultAction(x);
    }

    public void performActionOnArrayReference(ArrayReference x) {
	doDefaultAction(x);
    }

    public void performActionOnAssert(Assert x) {
        doDefaultAction(x);
    }

    public void performActionOnBinaryAnd(BinaryAnd x) {
	doDefaultAction(x);
    }

    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnBinaryNot(BinaryNot x) {
	doDefaultAction(x);
    } 

    public void performActionOnBinaryOr(BinaryOr x) {
	doDefaultAction(x);
    } 

    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
	doDefaultAction(x);
    } 

    public void performActionOnBinaryXOr(BinaryXOr x) {
	doDefaultAction(x);
    } 

    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
	doDefaultAction(x);
    } 

    public void performActionOnBooleanLiteral(BooleanLiteral x) {
	doDefaultAction(x);
    } 

    public void performActionOnBreak(Break x) {
	doDefaultAction(x);
    } 

    public void performActionOnCase(Case x) {
	doDefaultAction(x);
    } 

    public void performActionOnCatch(Catch x) {
	doDefaultAction(x);
    }
 
    public void performActionOnCatchAllStatement(CatchAllStatement x) {
	doDefaultAction(x);
    }
 

    public void performActionOnCharLiteral(CharLiteral x) {
	doDefaultAction(x);
    }
    
  /*  public void performActionOnCurrentMemoryAreaReference(CurrentMemoryAreaReference x){
        doDefaultAction(x);
    }*/
 
    public void performActionOnClassDeclaration(ClassDeclaration x) {
	doDefaultAction(x);
    }
 

    public void performActionOnClassInitializer(ClassInitializer x) {
	doDefaultAction(x);
    }
 

    public void performActionOnComment(Comment x) {
	doDefaultAction(x);
    }
 
    public void performActionOnCompilationUnit(CompilationUnit x) {
	doDefaultAction(x);
    }

    public void performActionOnConditional(Conditional x) {
	doDefaultAction(x);
    }

    public void performActionOnConstructorDeclaration
	(ConstructorDeclaration x) {
	doDefaultAction(x);
    }
 

    public void performActionOnContextStatementBlock(ContextStatementBlock x) {
	doDefaultAction(x);
    }

    public void performActionOnContinue(Continue x) {
	doDefaultAction(x);
    }
 
    public void performActionOnCopyAssignment(CopyAssignment x) {
	doDefaultAction(x);	
    }
    
    public void performActionOnSetAssignment(SetAssignment x) {
        doDefaultAction(x);
    }

    public void performActionOnDefault(Default x) {
	doDefaultAction(x);
    }

    public void performActionOnDivide(Divide x) {
	doDefaultAction(x);
    }
 
    public void performActionOnDivideAssignment(DivideAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnDo(Do x) {
	doDefaultAction(x);
    }
 
    public void performActionOnDoubleLiteral(DoubleLiteral x) {
	doDefaultAction(x);
    }

    public void performActionOnElse(Else x) {
	doDefaultAction(x);
    } 

    public void performActionOnEmptyStatement(EmptyStatement x)   {
	doDefaultAction(x);
    }

    public void performActionOnEquals(Equals x) {
	doDefaultAction(x);
    }

    public void performActionOnExactInstanceof(ExactInstanceof x) {
	doDefaultAction(x);
    }

    public void performActionOnExecutionContext(ExecutionContext x) {
	doDefaultAction(x);
    }
 
    public void performActionOnExtends(Extends x) {
	doDefaultAction(x);
    }
    
    public void performActionOnEnhancedFor(EnhancedFor x) {
        doDefaultAction(x);
    }

    public void performActionOnFieldDeclaration(FieldDeclaration x) {
	doDefaultAction(x);
    }
 
    public void performActionOnFieldReference(FieldReference x) {
	doDefaultAction(x);
    }
 
    public void performActionOnFieldSpecification(FieldSpecification x) {
	doDefaultAction(x);
    }
 
    public void performActionOnFinally(Finally x) {
	doDefaultAction(x);
    }
 
    public void performActionOnFloatLiteral(FloatLiteral x) {
	doDefaultAction(x);	
    } 

    public void performActionOnFor(For x) {
	doDefaultAction(x);
    } 

    public void performActionOnForUpdates(ForUpdates x) {
	doDefaultAction(x);
    } 

    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
	doDefaultAction(x);
    } 

    public void performActionOnGreaterThan(GreaterThan x) {
	doDefaultAction(x);
    }
 
    public void performActionOnGuard(Guard x) {
	doDefaultAction(x);
    }

    public void performActionOnIf(If x) {
	doDefaultAction(x);
    }

    public void performActionOnImplements(Implements x) {
	doDefaultAction(x);
    }

    public void performActionOnImplicitFieldSpecification(ImplicitFieldSpecification x) {
	doDefaultAction(x);
    }
 
    public void performActionOnImport(Import x) {
	doDefaultAction(x);
    }

    public void performActionOnInstanceof(Instanceof x) {
	doDefaultAction(x);
    }
 
    public void performActionOnInterfaceDeclaration(InterfaceDeclaration x) {
	doDefaultAction(x);
    }

    public void performActionOnIntLiteral(IntLiteral x) {
	doDefaultAction(x);
    }

    public void performActionOnLabeledStatement(LabeledStatement x) {
	doDefaultAction(x);
    }

    public void performActionOnLessOrEquals(LessOrEquals x) {
	doDefaultAction(x);
    }
 
    public void performActionOnLessThan(LessThan x) {
	doDefaultAction(x);
    }

    public void performActionOnLocalVariableDeclaration
	(LocalVariableDeclaration x) {
	doDefaultAction(x);		
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        // TODO: uncomment line below after KeY 1.0 and remove the call
        // to performActionOnProgramVariable        
        //doDefaultAction(x);
        performActionOnProgramVariable(x);
    }

    public void performActionOnLogicalAnd(LogicalAnd x) {
	doDefaultAction(x);
    }

    public void performActionOnLogicalNot(LogicalNot x) {
	doDefaultAction(x);
    }
 
    public void performActionOnLogicalOr(LogicalOr x) {
	doDefaultAction(x);
    }
 
    public void performActionOnLongLiteral(LongLiteral x) {
	doDefaultAction(x);	
    }
 
    public void performActionOnLoopInit(LoopInit x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMetaClassReference(MetaClassReference x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMethod(ProgramMethod x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMethodBodyStatement(MethodBodyStatement x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMethodDeclaration(MethodDeclaration x) {
	doDefaultAction(x);
    }

    public void performActionOnMethodFrame(MethodFrame x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMethodReference(MethodReference x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMinus(Minus x) {
	doDefaultAction(x);
    }
 
    public void performActionOnMinusAssignment(MinusAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnModifier(Modifier x) {
	doDefaultAction(x);
    }

    public void performActionOnModulo(Modulo x) {
	doDefaultAction(x);
    }

    public void performActionOnModuloAssignment(ModuloAssignment x) {
	doDefaultAction(x);
    }
 
    public void performActionOnNegative(Negative x) {
	doDefaultAction(x);
    }

    public void performActionOnNew(New x) {
	doDefaultAction(x);
    }
 
    public void performActionOnNewArray(NewArray x) {
	doDefaultAction(x);
    }

    public void performActionOnNotEquals(NotEquals x) {
	doDefaultAction(x);
    }
 
    public void performActionOnNullLiteral(NullLiteral x) {
	doDefaultAction(x);
    }
 
    public void performActionOnPackageReference(PackageReference x) {
	doDefaultAction(x);
    }
 
    public void performActionOnPackageSpecification(PackageSpecification x) {
	doDefaultAction(x);	
    }

    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
	doDefaultAction(x);
    }

    public void 
	performActionOnParenthesizedExpression(ParenthesizedExpression x) {
	doDefaultAction(x);
    }
 
    public void 
	performActionOnPassiveExpression(PassiveExpression x) {
	doDefaultAction(x);
    }
 
    public void performActionOnPlus(Plus x) {
	doDefaultAction(x);
    }

    public void performActionOnPlusAssignment(PlusAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnPositive(Positive x) {
	doDefaultAction(x);
    }

    public void performActionOnPostDecrement(PostDecrement x) {
	doDefaultAction(x);
    }
 
    public void performActionOnPostIncrement(PostIncrement x) {
	doDefaultAction(x);
    }

    public void performActionOnPreDecrement(PreDecrement x) {
	doDefaultAction(x);
    }

    public void performActionOnPreIncrement(PreIncrement x) {
	doDefaultAction(x);
    }
 
    public void performActionOnProgramConstant(ProgramConstant x) {
        // TODO: uncomment line below after KeY 1.0 and remove the call
        // to performActionOnProgramVariable        
        //doDefaultAction(x);
        performActionOnProgramVariable(x);
    }
 
    public void performActionOnProgramElementName(ProgramElementName x) {
	doDefaultAction(x);
    }

    public void performActionOnProgramMetaConstruct(ProgramMetaConstruct x) {
	doDefaultAction(x);
    }

    public void performActionOnProgramMethod(ProgramMethod x) {
	doDefaultAction(x);
    }
 
    public void performActionOnProgramSVProxy(ProgramSVProxy x)     {
	doDefaultAction(x);
    }
 
    public void performActionOnProgramSVSkolem(ProgramSVSkolem x)     {
	doDefaultAction(x);
    }
 
    public void performActionOnProgramVariable(ProgramVariable x) {
	doDefaultAction(x);
    }
 
    public void performActionOnReturn(Return x) {
	doDefaultAction(x);
    }
    
    public void performActionOnSchematicFieldReference
	(SchematicFieldReference x) {
	doDefaultAction(x);	
    }

    public void performActionOnSchemaVariable(SchemaVariable x) {
	doDefaultAction((ProgramSV)x);
    }


    public void performActionOnShiftLeft(ShiftLeft x) {
	doDefaultAction(x);
    }

 
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
	doDefaultAction(x);
    }
 
 
    public void performActionOnShiftRight(ShiftRight x) {
	doDefaultAction(x);
    }
 
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnStatementBlock(StatementBlock x) {
	doDefaultAction(x);
    }

    public void performActionOnStringLiteral(StringLiteral x) {
	doDefaultAction(x);
    }
    
    public void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x) {
	doDefaultAction(x);
    }

    public void performActionOnSuperConstructorReference
	(SuperConstructorReference x) {
	doDefaultAction(x);
    }

    public void performActionOnSuperReference(SuperReference x) {
	doDefaultAction(x);
    }

    public void performActionOnSwitch(Switch x) {
	doDefaultAction(x);
    }

    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
	doDefaultAction(x);
    }

    public void performActionOnThen(Then x) {
	doDefaultAction(x);
    }

    public void performActionOnThisConstructorReference 
	(ThisConstructorReference x) {
	doDefaultAction(x);
    }

    public void performActionOnThisReference(ThisReference x) {
	doDefaultAction(x);
    }

    public void performActionOnThrow(Throw x) {
	doDefaultAction(x);
    }

    public void performActionOnThrows(Throws x) {
	doDefaultAction(x);
    }

    public void performActionOnTimes(Times x) {
	doDefaultAction(x);
    }

    public void performActionOnTimesAssignment(TimesAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnTry(Try x) {
	doDefaultAction(x);
    }

    public void performActionOnTypeCast(TypeCast x) {
	doDefaultAction(x);
    }

    public void performActionOnTypeReference(TypeReference x) {
	doDefaultAction(x);
    }

    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x) {
	doDefaultAction(x);
    }


    public void performActionOnUnsignedShiftRightAssignment 
	(UnsignedShiftRightAssignment x) {
	doDefaultAction(x);
    }

    public void performActionOnVariableDeclaration(VariableDeclaration x) {
	doDefaultAction(x);
    }

    public void performActionOnVariableReference(VariableReference x) {
	doDefaultAction(x);
    }
    
    public void performActionOnVariableSpecification(VariableSpecification x) {
	doDefaultAction(x);
    }

    public void performActionOnWhile(While x) {
	doDefaultAction(x);
    }
    
    public void performActionOnLoopInvariant(LoopInvariant x) {
        //do nothing
    }
}
