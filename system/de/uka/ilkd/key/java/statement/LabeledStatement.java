// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Labeled statement.
 */

public class LabeledStatement extends JavaStatement 
    implements StatementContainer, 
	       NamedProgramElement, 
	       ProgramPrefix {

    /**
     *      Name.
     */

    protected final Label name;

    /**
     *      Body.
     */

    protected final Statement body;

    
    private final ImmutableArray<ProgramPrefix> prefixElementArray;


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: 	a Label (as name of the label)
     * 	        	a Statement (as body of the labeled statement)
     * 		        Comments	
     */
    public LabeledStatement(ExtList children, Label label, PositionInfo pos) {
	super(children, pos);
	name=label;	        

	body=(Statement)children.get(Statement.class);
        prefixElementArray = computePrefix(body);
    }

    /**
     *      Labeled statement.
     *      @param name an identifier.
     */

    public LabeledStatement(Label name) {
	this.name=name;
	body=new EmptyStatement();
        prefixElementArray = new ImmutableArray<ProgramPrefix>();
    }

    /**
     *      Labeled statement.
     *      @param id a Label.
     *      @param statement a statement.
     */

    public LabeledStatement(Label id, Statement statement) {
        this.name=id;
        body=statement;
        prefixElementArray = computePrefix(body);
    }


    private ImmutableArray<ProgramPrefix> computePrefix(Statement b) {
        if (b instanceof StatementBlock) {
            return StatementBlock.computePrefixElements
            (((StatementBlock)b).getBody(), 0, this);
        } else if (b instanceof ProgramPrefix) {
            return StatementBlock.
                computePrefixElements(new ImmutableArray<Statement>(b), 
                        0, this);
        }        
        return new ImmutableArray<ProgramPrefix>(this);
    }
    
    public int getPrefixLength() {        
        return prefixElementArray.size();
    }

    public ProgramPrefix getPrefixElementAt(int i) {       
        return prefixElementArray.get(i);
    }

    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return prefixElementArray;
    }


    public SourceElement getFirstElement() {
        return getBody().getFirstElement();
    }

    public SourceElement getLastElement() {
        return body.getLastElement();
    }


    /**
     *      Get name.
     *      @return the string.
     */

    public final String getName() {
        return (name == null) ? null : name.toString();
    }

    /**
     *      Get identifier.
     *      @return the identifier.
     */

    public Label getLabel() {
        return name;
    }


    /**
     *      Get identifier.
     *      @return the identifier.
     */
    public ProgramElementName getProgramElementName() {
	if ((name instanceof ProgramElementName) || (name==null)) {
	    return (ProgramElementName) name;
	} 
	Debug.out("labeledstatement: SCHEMAVARIABLE IN LABELEDSTATEMENT");
	return null;
    }

    /**
     *      Get body.
     *      @return the statement.
     */
    public Statement getBody() {
        return body;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (name != null) result++;
        if (body != null) result++;
        return result;
    }

    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (name != null) {
            if (index == 0) return name;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    
    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /**
     *       Return the statement at the specified index in this node's
     *       "virtual" statement array.
     *       @param index an index for a statement.
     *       @return the statement with the given index.
     *       @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *       of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnLabeledStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printLabeledStatement(this);
    }

    /** testing if programelements are equal modulo renaming abstract
     * from names. Therefore declaration of label names have to be
     * mapped to the same abstract name. This is done here.
     */
    public boolean equalsModRenaming(SourceElement se, 
				     NameAbstractionTable nat) {
	if (!(se instanceof LabeledStatement)) {
	    return false;
	}
	final LabeledStatement lSt = (LabeledStatement)se;	
	nat.add(getLabel(), lSt.getLabel());
	return super.equalsModRenaming(lSt, nat);
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + getChildCount();
    	for (int i = 0; i<getChildCount(); i++) {
    		result = 37 * result + getChildAt(i).hashCode();
    	}
    	return result;
    }
    
    public boolean equals(Object o){
    	return super.equals(o);
    }
    
    
    private PosInProgram firstActiveChildPos = null;
    
    public PosInProgram getFirstActiveChildPos() {
        if (firstActiveChildPos == null) {                   
            firstActiveChildPos = body instanceof StatementBlock ? 
                    (((StatementBlock)body).isEmpty() ? PosInProgram.TOP : 
                        PosInProgram.TOP.down(1).down(0))
                        : PosInProgram.TOP.down(1);
        }
        return firstActiveChildPos;
    }
    
}
