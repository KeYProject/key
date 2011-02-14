// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramMetaConstruct;
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
    
    
    @Override
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
    @Override    
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }
    

    /** the action that is performed just before leaving the node the
     * last time 
     */    
    protected abstract void doDefaultAction(SourceElement node) ;

    @Override    
    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
	doDefaultAction(x);
    }

    @Override    
    public void performActionOnArrayDeclaration(ArrayDeclaration x) {
	doDefaultAction(x);
    }
    
    @Override    
    public void performActionOnArrayInitializer(ArrayInitializer x) {
	doDefaultAction(x);
    }

    @Override    
    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
	doDefaultAction(x);
    }

    @Override    
    public void performActionOnArrayReference(ArrayReference x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnAssert(Assert x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnBinaryAnd(BinaryAnd x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnBinaryNot(BinaryNot x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnBinaryOr(BinaryOr x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnBinaryXOr(BinaryXOr x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnBooleanLiteral(BooleanLiteral x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnEmptySetLiteral(EmptySetLiteral x) {
	doDefaultAction(x);
    }
        
    @Override
    public void performActionOnSingleton(Singleton x) {
	doDefaultAction(x);
    }                     
    
    @Override
    public void performActionOnSetUnion(SetUnion x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnIntersect(Intersect x) {
	doDefaultAction(x);
    }         

    @Override
    public void performActionOnSetMinus(SetMinus x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnAllFields(AllFields x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnEmptySeqLiteral(EmptySeqLiteral x) {
	doDefaultAction(x);
    }    

    @Override
    public void performActionOnSeqSingleton(SeqSingleton x) {
	doDefaultAction(x);
    }    
    
    @Override
    public void performActionOnSeqConcat(SeqConcat x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnSeqSub(SeqSub x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnSeqReverse(SeqReverse x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnBreak(Break x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnCase(Case x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnCatch(Catch x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnCatchAllStatement(CatchAllStatement x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnCharLiteral(CharLiteral x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnClassDeclaration(ClassDeclaration x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnClassInitializer(ClassInitializer x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnComment(Comment x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnCompilationUnit(CompilationUnit x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnConditional(Conditional x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnConstructorDeclaration
	(ConstructorDeclaration x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnContextStatementBlock(ContextStatementBlock x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnContinue(Continue x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
	doDefaultAction(x);	
    }
    
    @Override
    public void performActionOnDefault(Default x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnDivide(Divide x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnDivideAssignment(DivideAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnDo(Do x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnDoubleLiteral(DoubleLiteral x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnElse(Else x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnEmptyStatement(EmptyStatement x)   {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnEquals(Equals x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnExactInstanceof(ExactInstanceof x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnExecutionContext(ExecutionContext x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnExtends(Extends x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnEnhancedFor(EnhancedFor x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnFieldDeclaration(FieldDeclaration x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnFieldReference(FieldReference x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnFieldSpecification(FieldSpecification x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnFinally(Finally x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnFloatLiteral(FloatLiteral x) {
	doDefaultAction(x);	
    } 

    @Override
    public void performActionOnFor(For x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnForUpdates(ForUpdates x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
	doDefaultAction(x);
    } 

    @Override
    public void performActionOnGreaterThan(GreaterThan x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnGuard(Guard x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnIf(If x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnImplements(Implements x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnImplicitFieldSpecification(ImplicitFieldSpecification x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnImport(Import x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnInstanceof(Instanceof x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnInterfaceDeclaration(InterfaceDeclaration x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnIntLiteral(IntLiteral x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnLabeledStatement(LabeledStatement x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnLessOrEquals(LessOrEquals x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnLessThan(LessThan x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnLocalVariableDeclaration
	(LocalVariableDeclaration x) {
	doDefaultAction(x);		
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        // TODO: uncomment line below after KeY 1.0 and remove the call
        // to performActionOnProgramVariable        
        //doDefaultAction(x);
        performActionOnProgramVariable(x);
    }

    @Override
    public void performActionOnLogicalAnd(LogicalAnd x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnLogicalNot(LogicalNot x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnLogicalOr(LogicalOr x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnLongLiteral(LongLiteral x) {
	doDefaultAction(x);	
    }
 
    @Override
    public void performActionOnLoopInit(LoopInit x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMetaClassReference(MetaClassReference x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMethod(ProgramMethod x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMethodBodyStatement(MethodBodyStatement x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMethodDeclaration(MethodDeclaration x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnMethodFrame(MethodFrame x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMethodReference(MethodReference x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMinus(Minus x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnMinusAssignment(MinusAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnModifier(Modifier x) {
	doDefaultAction(x);
    }

    public void performActionOnModulo(Modulo x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnModuloAssignment(ModuloAssignment x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnNegative(Negative x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnNew(New x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnNewArray(NewArray x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnNotEquals(NotEquals x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnNullLiteral(NullLiteral x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnPackageReference(PackageReference x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnPackageSpecification(PackageSpecification x) {
	doDefaultAction(x);	
    }

    @Override
    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
	doDefaultAction(x);
    }

    @Override
    public void 
	performActionOnParenthesizedExpression(ParenthesizedExpression x) {
	doDefaultAction(x);
    }
 
    @Override
    public void 
	performActionOnPassiveExpression(PassiveExpression x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnPlus(Plus x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnPlusAssignment(PlusAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnPositive(Positive x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnPostDecrement(PostDecrement x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnPostIncrement(PostIncrement x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnPreDecrement(PreDecrement x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnPreIncrement(PreIncrement x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnProgramConstant(ProgramConstant x) {
        // TODO: uncomment line below after KeY 1.0 and remove the call
        // to performActionOnProgramVariable        
        //doDefaultAction(x);
        performActionOnProgramVariable(x);
    }
 
    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramMetaConstruct(ProgramMetaConstruct x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramMethod(ProgramMethod x) {
	doDefaultAction(x);
    }
  
    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnIProgramVariable(IProgramVariable x) {
        doDefaultAction(x);
    }
 
    @Override
    public void performActionOnReturn(Return x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnSchematicFieldReference
	(SchematicFieldReference x) {
	doDefaultAction(x);	
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
	doDefaultAction((ProgramSV)x);
    }

    @Override
    public void performActionOnShiftLeft(ShiftLeft x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnShiftRight(ShiftRight x) {
	doDefaultAction(x);
    }
 
    @Override
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnStatementBlock(StatementBlock x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnStringLiteral(StringLiteral x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnSuperConstructorReference
	(SuperConstructorReference x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnSuperReference(SuperReference x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnSwitch(Switch x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnThen(Then x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnThisConstructorReference 
	(ThisConstructorReference x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnThisReference(ThisReference x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnThrow(Throw x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnThrows(Throws x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnTimes(Times x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnTimesAssignment(TimesAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnTry(Try x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnTypeCast(TypeCast x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnTypeReference(TypeReference x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnUnsignedShiftRightAssignment 
	(UnsignedShiftRightAssignment x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnVariableDeclaration(VariableDeclaration x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnVariableReference(VariableReference x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnVariableSpecification(VariableSpecification x) {
	doDefaultAction(x);
    }

    @Override
    public void performActionOnWhile(While x) {
	doDefaultAction(x);
    }
    
    @Override
    public void performActionOnLoopInvariant(LoopInvariant x) {
        //do nothing
    }
}
