// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import java.io.IOException;

import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/** 
 * In the DL-formulae description of Taclets the program part can have
 * the following form < pi alpha;...; omega > Phi where pi is a prefix
 * consisting of open brackets, try's and so on and omega is the rest
 * of the program. Between the prefix pi and the postfix omega there
 * can stand an arbitrary program. This pattern is realized using this
 * class.
 */

public class ContextStatementBlock extends StatementBlock {


    /** 
     * the last execution context of the context term 
     */
    private IExecutionContext executionContext;

    /** creates a ContextStatementBlock 
     * @param children the body of the context term
     */
    public ContextStatementBlock(ExtList children) {
	super(children);
    }

    /** creates a ContextStatementBlock 
     * @param children the body of the context term
     * @param executionContext the required execution context
     */
    public ContextStatementBlock(ExtList children, 
		       IExecutionContext executionContext) {
	super(children);
	this.executionContext = executionContext;
    }

    public ContextStatementBlock(Statement s, 
               IExecutionContext executionContext) {
        super(s);
        this.executionContext = executionContext;
    }
    
    public ContextStatementBlock(Statement[] body, 
               IExecutionContext executionContext) {
        super(body);
        this.executionContext = executionContext;
    }

    public boolean requiresExplicitExecutionContextMatch() {
	return executionContext != null;
    }

    public IExecutionContext getExecutionContext() {
	return executionContext;
    }

    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
    */

    public int getChildCount() {
	int count = 0;
	if (executionContext != null) count++;
	count += super.getChildCount();
        return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     * of bounds
     */
    public ProgramElement getChildAt(int index) {
	if (executionContext != null) {
	    if (index == 0) {
		return executionContext;
	    } 
	    index--;
	}
	return super.getChildAt(index);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnContextStatementBlock(this);
    }

    public void prettyPrint(PrettyPrinter w) throws IOException {
	w.printContextStatementBlock(this);
    }
    
    /* toString */
    public String toString() {
	StringBuffer result = new StringBuffer();
	result.append("..");
	result.append(super.toString());
	result.append("\n");
	result.append("...");
	return result.toString();
    }
    
    

    public int getTypeDeclarationCount() {
        throw new UnsupportedOperationException(getClass()+
            ": We are not quite a StatementBlock");
    }

    public de.uka.ilkd.key.java.declaration.TypeDeclaration 
                                            getTypeDeclarationAt(int index) {
        throw new UnsupportedOperationException(getClass()+
            ": We are not quite a StatementBlock");
    }

    /**
     * overrides the check of the superclass as unmatched elements will disappear in 
     * the suffix of this ContextStatementBlock
     */
    public boolean compatibleBlockSize(int pos, int max) {
        return true;
    }        
    
    
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        SourceData newSource = source;
        
        if (matchCond.getInstantiations().
                getContextInstantiation() != null) {
            // Currently we do not allow to context statement block 
            // occurrences in find or assumes clauses
            return null;
        }
        
        final ProgramElement src = newSource.getSource();
        final Services services  = source.getServices();
        
        ExecutionContext lastExecutionContext = null;
               
        final ProgramPrefix prefix;
        int pos = -1;
        PosInProgram relPos = PosInProgram.TOP;                         
        
        if (src instanceof ProgramPrefix) {
            prefix = (ProgramPrefix)src;            
            final int srcPrefixLength     = prefix.getPrefixLength();
            final int patternPrefixLength = getPrefixLength();
                        
            if (patternPrefixLength > srcPrefixLength) {
                Debug.out("Program match FAILED. Source has not enough prefix elements.", 
                        this, source);
                return null;
            }
     
            pos = srcPrefixLength - patternPrefixLength;
            
            ProgramPrefix firstActiveStatement = prefix.getPrefixElementAt(pos);                                                                                            
            
            relPos = firstActiveStatement.getFirstActiveChildPos();
            
            // firstActiveStatement contains the ProgramPrefix in front of the first active statement
            // start denotes the child where to start to match
            // in some cases firstActiveStatement already denotes the element to match
            // (empty block, empty try block etc.) this is encoded by setting start to -1
            int start = -1;
            
            if (relPos != PosInProgram.TOP) {                
                if (firstActiveStatement instanceof MethodFrame) {
                    lastExecutionContext = (ExecutionContext) 
                        ((MethodFrame)firstActiveStatement).
                        getExecutionContext();
                }              
         
                start = relPos.get(relPos.depth()-1);                                                    
                if (relPos.depth()>1) {
                    firstActiveStatement = (ProgramPrefix)
                      PosInProgram.getProgramAt(relPos.up(), 
                              firstActiveStatement);
                }
            }
            newSource = new SourceData(firstActiveStatement, start, services);                        
        } else {
            prefix = null;
        }
        matchCond = matchInnerExecutionContext(matchCond, services, 
                lastExecutionContext, prefix, pos, src);                
        
        if (matchCond == null) {
            return null;
        }          
        
        // matching children
        matchCond = matchChildren(newSource, matchCond, 
                executionContext == null ? 0 : 1);                
        
        if (matchCond == null) {
            return null;
        }
            
        matchCond = makeContextInfoComplete(matchCond,
        				    newSource, 
        				    prefix, 
        				    pos, 
        				    relPos, 
        				    src,
        				    services);
        
        if (matchCond == null) {
            return null;
        }       
        
        Debug.out("Successful match.");
        return matchCond;
    }

    /**
     * completes match of context block by adding the prefix end position
     * and the suffix start position
     */
    private MatchConditions makeContextInfoComplete(
	    MatchConditions matchCond, 
            SourceData newSource, 
            ProgramPrefix prefix, 
            int pos, 
            PosInProgram relPos, 
            ProgramElement src,
            Services services) {
        
        final SVInstantiations instantiations = matchCond.getInstantiations();        
        final ExecutionContext lastExecutionContext = instantiations.getExecutionContext();
       
        final PosInProgram prefixEnd = matchPrefixEnd(prefix, pos, relPos);
        
        // compute position of the first element not matched        
        final int lastMatchedPos = newSource.getChildPos();                
        final PosInProgram suffixStart = prefixEnd.up().down(lastMatchedPos); 
                
        /** add context block instantiation */
        matchCond = matchCond.setInstantiations
            (instantiations.replace(prefixEnd, 
        	    		    suffixStart, 
        	    		    lastExecutionContext, 
        	    		    src,
        	    		    services));
        return matchCond;
    }

    /**
     * matches the inner most execution context in prefix, used to resolve references in
     * succeeding matchings
     * @param matchCond the MatchCond the matchonditions already found 
     * @param services the Services
     * @param lastExecutionContext the ExecutionContext if already found 
     * @param prefix the oute rmost prefixelement of the original source
     * @param pos an int as the number of prefix elements to disappear in the context
     * @param src the original source
     * @return the inner most execution context
     */
    private MatchConditions matchInnerExecutionContext(MatchConditions matchCond, 
            final Services services, ExecutionContext lastExecutionContext, 
            final ProgramPrefix prefix, int pos, final ProgramElement src) {
        
        // partial context instantiation
        
        ExecutionContext innerContext = lastExecutionContext;
        
        if (innerContext == null) {
            innerContext = services.getJavaInfo().getDefaultExecutionContext();
            if (prefix != null) {            
                for (int i = pos - 1; i>=0; i--) {
                    final ProgramPrefix prefixEl = prefix.getPrefixElementAt(i);                                   
                    if (prefixEl instanceof MethodFrame) {
                        innerContext = (ExecutionContext) 
                        ((MethodFrame)prefixEl).getExecutionContext();
                        break;
                    } 
                }                
            }
        }
        
        if (executionContext != null) {
            matchCond = executionContext.match(new SourceData(innerContext, -1, 
                    services), matchCond);
            if (matchCond == null) {
                Debug.out("Program match. ExecutionContext mismatch.");
                return null;
            }
            Debug.out("Program match. ExecutionContext matched.");
        }
      
        matchCond = 
            matchCond.setInstantiations(matchCond.getInstantiations().
                    add(null, 
                	null, 
                	innerContext, 
                	src,
                	services));
        
        return matchCond;
    }

    /**
     * computes the PosInProgram of the first element, which is not part of the prefix
     * @param prefix the ProgramPrefix the outer most prefix element of the source
     * @param pos the number of elements to disappear in the context
     * @param relPos the position of the first active statement of element
     *  prefix.getPrefixElementAt(pos);
     * @return the PosInProgram of the first element, which is not part of the prefix
     */
    private PosInProgram matchPrefixEnd(final ProgramPrefix prefix, int pos, PosInProgram relPos) {
        PosInProgram prefixEnd = PosInProgram.TOP;
        if (prefix != null) {            
            final IntIterator[] iterators = new IntIterator[pos + 1];
            iterators[pos] = relPos.iterator();
            
            for (int i = pos - 1; i>=0; i--) {
                final ProgramPrefix prefixEl = prefix.getPrefixElementAt(i);                          
                iterators[i] = prefixEl.getFirstActiveChildPos().iterator();               
            }

            for (final IntIterator it : iterators) {
                while (it.hasNext()) {
                    prefixEnd = prefixEnd.down(it.next());
                }
            }
        } else {
            prefixEnd = relPos;
        }
        return prefixEnd;
    }
}
