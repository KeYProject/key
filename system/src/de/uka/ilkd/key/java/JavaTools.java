package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.ExtList;

/** Miscellaneous static methods related to Java blocks or statements in KeY.
 * Mostly moved from key.util.MiscTools here.
 * @author bruns
 *
 */
public final class JavaTools {

    /**
     * Returns the active statement of the passed a java block.
     */
    public static SourceElement getActiveStatement(JavaBlock jb) {
    assert jb.program() != null;
    
        SourceElement result = jb.program().getFirstElement();
        while((result instanceof ProgramPrefix 
        	 || result instanceof CatchAllStatement)
              && !(result instanceof StatementBlock 
                   && ((StatementBlock)result).isEmpty())) {
            if(result instanceof LabeledStatement) {
                result = ((LabeledStatement)result).getChildAt(1);
            } else if(result instanceof CatchAllStatement) {
        	result = ((CatchAllStatement)result).getBody();
            } else {
                result = result.getFirstElement();
            }
        }
        return result;
    }

    public static StatementBlock getActiveBlock(JavaBlock jb) {
        assert jb.program() != null;
        SourceElement element = jb.program().getFirstElement();
        SourceElement parent = element;
        while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
                && !(element instanceof StatementBlock && ((StatementBlock) element).isEmpty())) {
            parent = element;
            if (element instanceof LabeledStatement) {
                element = ((LabeledStatement) element).getChildAt(1);
            }
            else if (element instanceof CatchAllStatement) {
                element = ((CatchAllStatement) element).getBody();
            }
            else if (element instanceof StatementContainer) {
                element = ((StatementContainer) element).getStatementAt(0);
            }
            else {
                element = element.getFirstElement();
            }
        }
        if (parent instanceof StatementBlock) {
            return (StatementBlock) parent;
        }
        return null;
    }
    
    /**
     * Returns the passed java block without its active statement.
     */
    public static JavaBlock removeActiveStatement(JavaBlock jb, 
                              Services services) {
        assert jb.program() != null;
        final SourceElement activeStatement = JavaTools.getActiveStatement(jb);
        Statement newProg = (Statement)
            (new CreatingASTVisitor(jb.program(), false, services) {
                private boolean done = false;
                
                public ProgramElement go() {
                    stack.push(new ExtList());
                    walk(root());
                    ExtList el = stack.peek();
                    return el.get(ProgramElement.class); 
                }
                
                public void doAction(ProgramElement node) {
                    if(!done && node == activeStatement) {
                        done = true;
                        stack.pop();                    
                        changed();
                    } else {
                        super.doAction(node);
                    }
                }
            }).go();
        
        StatementBlock newSB = newProg instanceof StatementBlock 
                               ? (StatementBlock)newProg
                               : new StatementBlock(newProg);              
        return JavaBlock.createJavaBlock(newSB);
    }


    
    
    /**
     * Returns the innermost method frame of the passed java block
     */
    public static MethodFrame getInnermostMethodFrame(JavaBlock jb, 
                                      Services services) { 
        final ProgramElement pe = jb.program();
        final MethodFrame result = new JavaASTVisitor(pe, services) {
            private MethodFrame res;
            protected void doAction(ProgramElement node) {
                node.visit(this);
            }
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && res == null) {
                    res = (MethodFrame) node;
                }
            }
            public MethodFrame run() {
                walk(pe);
                return res;
            }
        }.run();
                
        return result;
    }
    

    public static ExecutionContext getInnermostExecutionContext(
        						JavaBlock jb, 
        						Services services) {
    final MethodFrame frame = getInnermostMethodFrame(jb, services);
    return frame == null 
               ? null
           : (ExecutionContext) frame.getExecutionContext();	
    }
    
}
