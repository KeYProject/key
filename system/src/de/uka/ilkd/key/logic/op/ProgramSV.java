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


package de.uka.ilkd.key.logic.op;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.Throws;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramConstruct;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.ProgramList;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.Debug;

/**
 * Objects of this class are schema variables matching program constructs 
 * within modal operators. The particular construct being matched is
 * determined by the ProgramSVSort of the schema variable.
 */
public final class ProgramSV extends AbstractSV 
    implements ProgramConstruct, UpdateableOperator {
    
    private static final ProgramList EMPTY_LIST_INSTANTIATION 
    	= new ProgramList(new ImmutableArray<ProgramElement>(
    					new ProgramElement[0]));

    private final boolean isListSV;

    
    /** 
     * creates a new SchemaVariable used as a placeholder for program
     * constructs
     * @param name the Name of the SchemaVariable
     * allowed to match a list of program constructs
     */    
    ProgramSV(Name name, ProgramSVSort s, boolean isListSV) {
	super(name, s, false, false);
	this.isListSV = isListSV;
    }
    
    
    public boolean isListSV() {
	return isListSV;
    }
    
    
    /** 
     * this method tests on object identity
     */
    @Override
    public boolean equalsModRenaming(SourceElement se, 
				     NameAbstractionTable nat) {
	return se == this;
    }    
        
    
    /** @return comments if the schemavariable stands for programm
     * construct and has comments attached to it (not supported yet)
     */
    @Override
    public Comment[] getComments() {
	return new Comment[0];
    }
    
    
    @Override
    public SourceElement getFirstElement(){
	return this;
    }
    
    
    @Override
    public SourceElement getLastElement(){
	return this;
    }
    

    @Override
    public Position getStartPosition(){
	return Position.UNDEFINED;
    }
    
    
    @Override
    public Position getEndPosition(){
	return Position.UNDEFINED;
    }

    
    @Override
    public Position getRelativePosition(){
	return  Position.UNDEFINED;
    }
    

    @Override
    public PositionInfo getPositionInfo(){
        return  PositionInfo.UNDEFINED;
    }


    @Override
    public ReferencePrefix getReferencePrefix() {
        return null;
    }


    @Override
    public int getDimensions(){
        return 0;
    }

    
    @Override
    public int getTypeReferenceCount(){
        return 0;
    }


    @Override
    public TypeReference getTypeReferenceAt(int index) {
        return this;
    }


    @Override
    public PackageReference getPackageReference() {
        return null;
    }

    
    @Override
    public int getExpressionCount() {
        return 0;
    }

    
    @Override
    public Expression getExpressionAt(int index) {
        return null;
    }

    
    @Override
    public int getChildCount() {
        return 0;
    }

    
    @Override
    public ProgramElement getChildAt(int index) {
        return this;
    }

    
    @Override
    public int getStatementCount() {
        return 0;
    }

    
    @Override
    public int size() {
        return 0;
    }

    @Override
	public ImmutableArray<Expression> getUpdates() {
        return null;
    }    

	@Override
    public ImmutableArray<LoopInitializer> getInits() {
        return null;
    }


    @Override
    public Statement getStatementAt(int i) {
        return this;
    }


    @Override
    public ProgramElementName getProgramElementName() {
        return new ProgramElementName(toString());
    }    

    
    @Override
    public String getName() {
        return name().toString();
    }

    
    @Override
    public void visit(Visitor v) {
        v.performActionOnSchemaVariable(this);
    }

    
    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {       
        w.printSchemaVariable(this);
    }

    
    @Override
    public KeYJavaType getKeYJavaType() {
        return null;
    }

    
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return null;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return null;
    }
  
    
    @Override
    public MatchConditions match(SVSubstitute substitute, 
				 MatchConditions mc, 
				 Services services) {

        final ProgramSVSort svSort = (ProgramSVSort)sort();
     
	if (substitute instanceof Term && svSort.canStandFor((Term)substitute)) {
            return addInstantiation((Term)substitute, mc, services);
        } else if (substitute instanceof ProgramElement && 
		   svSort.canStandFor((ProgramElement)substitute, 
				      mc.getInstantiations().getExecutionContext(), services)) {
            return addInstantiation((ProgramElement)substitute, mc, services);
        }        
        Debug.out("FAILED. Cannot match ProgramSV with given " +
		  "instantiation(template, orig)", this, substitute);
        return null;
    }

        
    /**
     * adds a found mapping from schema variable <code>var</code> to
     * program element <code>pe</code> and returns the updated match
     * conditions or null if mapping is not possible because of
     * violating some variable condition
     * @param pe the ProgramElement <code>var</code> is mapped to
     * @param matchCond the MatchConditions to be updated
     * @param services the Services provide access to the Java model
     * @return the updated match conditions including mapping 
     * <code>var</code> to <code>pe</code> or null if some variable
     * condition would be hurt by the mapping
     */
    private MatchConditions addProgramInstantiation(ProgramElement pe,
                                                    MatchConditions matchCond,
                                                    Services services) {
        if (matchCond == null) {
            return null;
        }

	SVInstantiations insts = matchCond.getInstantiations();

        final Object foundInst = insts.getInstantiation(this);	

	if (foundInst != null) {
	    final Object newInst;
	    if (foundInst instanceof Term) {
		newInst = services.getTypeConverter().
		    convertToLogicElement(pe, insts.getExecutionContext());
	    } else {
		newInst = pe;
	    }

	    if (foundInst.equals(newInst)) {
		return matchCond;
	    } else {
		return null;
	    }
	}

	insts = insts.add(this, pe, services);
	return insts == null ? null : matchCond.setInstantiations(insts);
    }

    /**
     * adds a found mapping from schema variable <code>var</code> to the
     * list of program elements <code>list</code> and returns the updated
     * match conditions or null if mapping is not possible because of
     * violating some variable condition
     * @param list the ProgramList <code>var</code> is mapped to
     * @param matchCond the MatchConditions to be updated
     * @param services the Services provide access to the Java model
     * @return the updated match conditions including mapping 
     * <code>var</code> to <code>list</code> or null if some variable
     * condition would be hurt by the mapping
     */
    private MatchConditions addProgramInstantiation(ProgramList list,
                                                    MatchConditions matchCond,
                                                    Services services) {
	if (matchCond == null) {
            return null;
        }

        SVInstantiations insts = matchCond.getInstantiations();
        final ProgramList pl = (ProgramList) insts.getInstantiation(this);        
        if (pl != null) {
	    if (pl.equals(list)) {
                return matchCond;
	    } else {
		return null;            
	    }
	}

        insts = insts.add(this, list, services);
        return insts == null ? null : matchCond.setInstantiations(insts);
    }
    
    
    private MatchConditions matchListSV(SourceData source, MatchConditions matchCond) {
	final Services services = source.getServices();
	ProgramElement src = source.getSource();

	if (src == null) {
	    return addProgramInstantiation(EMPTY_LIST_INSTANTIATION, matchCond, services);
	}

	SVInstantiations instantiations = matchCond.getInstantiations();

	final ExecutionContext ec = instantiations.getExecutionContext();        

	final java.util.ArrayList<ProgramElement> matchedElements = 
	    new java.util.ArrayList<ProgramElement>();        

	while (src != null) {
	    if (!check(src, ec, services)) {
		Debug.out("taclet: Stopped list matching because of " +
			"incompatible elements", this, src);
		break;
	    }
	    matchedElements.add(src);            
	    source.next();
	    src = source.getSource();
	}

	Debug.out("Program list match: ", this, matchedElements);
	return addProgramInstantiation(new ProgramList(new ImmutableArray<ProgramElement>(matchedElements)), 
		matchCond, services);
    }   
    

    /** 
     * returns true, if the given SchemaVariable can stand for the
     * ProgramElement 
     * @param match the ProgramElement to be matched
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return true if the SchemaVariable can stand for the given element
     */
    private boolean check(ProgramElement match,
                          ExecutionContext ec,
                          Services services) {        
        if (match == null) {           
            return false;
        }
        return ((ProgramSVSort)sort()).canStandFor(match, ec, services);
    }
        

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {  
	if(isListSV()) {
	    return matchListSV(source, matchCond);
        }	
	
        final Services services  = source.getServices();        
        final ProgramElement src = source.getSource();        
        Debug.out("Program match start (template, source)", this, src);

        final SVInstantiations instantiations = matchCond.getInstantiations();
        
        final ExecutionContext ec = instantiations.getExecutionContext(); 
        
        if (!check(src, ec, services)) {
            Debug.out("taclet: MATCH FAILED. Sort of SchemaVariable cannot "+
            "stand for the program");
            return null; //FAILED
        }
 
        final Object instant = instantiations.getInstantiation(this);
        if ( instant == null || instant.equals(src) ||
                ( instant instanceof Term && 
                        ((Term)instant).op().equals(src))) {
            
            matchCond = addProgramInstantiation(src, matchCond, services);
                     
            if (matchCond == null) {
                // FAILED due to incompatibility with already found matchings 
                // (e.g. generic sorts)
                return null; 
            }             
        } else {            
            Debug.out("taclet: MATCH FAILED 3. Former match of "+
                    " SchemaVariable incompatible with " +
		      " the current match.");
            return null; //FAILED mismatch            
        }
        source.next();   
        return matchCond;
    }
    
    
    @Override
    public String toString() {
	return toString("program "+sort().name());
    }
    

    @Override
    public String proofToString() {
	return "\\schemaVar \\program " + sort().declarationString() + " " + name() + ";\n";
    }


   @Override
   public MethodDeclaration getMethodDeclaration() {
      return null;
   }


   @Override
   public KeYJavaType getParameterType(int i) {
      return null;
   }


   @Override
   public StatementBlock getBody() {
      return null;
   }


   @Override
   public boolean isConstructor() {
      return false;
   }


   @Override
   public boolean isModel() {
      return false;
   }

   @Override
   public int getStateCount() {
      return 1;
   }

   @Override
   public int getHeapCount(Services services) {
      return HeapContext.getModHeaps(services, false).size();
   }

   @Override
   public boolean isVoid() {
      return false;
   }


   @Override
   public KeYJavaType getReturnType() {
      return null;
   }


   @Override
   public String getFullName() {
      return null;
   }


   @Override
   public boolean isAbstract() {
      return false;
   }


   @Override
   public boolean isImplicit() {
      return false;
   }


   @Override
   public boolean isNative() {
      return false;
   }


   @Override
   public boolean isFinal() {
      return false;
   }


   @Override
   public boolean isSynchronized() {
      return false;
   }


   @Override
   public Throws getThrown() {
      return null;
   }


   @Override
   public ParameterDeclaration getParameterDeclarationAt(int index) {
      return null;
   }


   @Override
   public VariableSpecification getVariableSpecification(int index) {
      return null;
   }


   @Override
   public int getParameterDeclarationCount() {
      return 0;
   }


   @Override
   public ImmutableArray<ParameterDeclaration> getParameters() {
      return null;
   }


   @Override
   public boolean isPrivate() {
      return false;
   }


   @Override
   public boolean isProtected() {
      return false;
   }


   @Override
   public boolean isPublic() {
      return false;
   }


   @Override
   public boolean isStatic() {
      return false;
   }


   @Override
   public boolean isStrictFp() {
      return false;
   }


   @Override
   public ImmutableArray<Modifier> getModifiers() {
      return null;
   }


   @Override
   public ImmutableArray<KeYJavaType> getParamTypes() {
      return null;
   }


   @Override
   public KeYJavaType getType() {
      return null;
   }


   @Override
   public KeYJavaType getContainerType() {
      return null;
   }


   @Override
   public int getNumParams() {
      return 0;
   }


   @Override
   public KeYJavaType getParamType(int i) {
      return null;
   }


   @Override
   public TypeReference getTypeReference() {
      return null;
   }


   @Override
   public IProgramMethod getMethodContext() {
      return null;
   }


   @Override
   public ReferencePrefix getRuntimeInstance() {
      return null;
   }
}
