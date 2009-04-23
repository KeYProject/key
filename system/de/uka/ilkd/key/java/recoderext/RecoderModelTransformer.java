// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.*;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.*;
import recoder.kit.TwoPassTransformation;
import recoder.service.DefaultCrossReferenceSourceInfo;
import de.uka.ilkd.key.util.Debug;

/**
 * The Java DL requires some implicit fields, that are available in each
 * Java class. The name of the implicit fields is usually enclosed
 * between two angle brackets. 
 * To access the fields in a uniform way, they are added as usual
 * fields to the classes, in particular this allows us to parse them in
 * more easier.
 *   For further information see also
 *   <ul>
 *     <li> {@link ImplicitFieldAdder} </li>
 *     <li> {@link CreateObjectBuilder}  </li>
 *     <li> {@link PrepareObjectBuilder} </li>
 *   </ul>
 *   
 * Performance of these classes was low, so information that is shared between
 * all instances of a transformation set has been outsourced to a transformation
 * cache.
 */
public abstract class RecoderModelTransformer extends TwoPassTransformation {

    protected CrossReferenceServiceConfiguration services;
    // protected List<CompilationUnit> units;
    protected TransformerCache cache;

    /**
     * creates a transormder for the recoder model
     * @param services the CrossReferenceServiceConfiguration to access
     * model information 
     * @param cache a cache object that stores information which is needed by
     * and common to many transformations. it includes the compilation units,
     * the declared classes, and information for local classes.
     */
    public RecoderModelTransformer
	(CrossReferenceServiceConfiguration services, 
	 TransformerCache cache) {	
	super(services);
	this.services = services;
	assert cache != null;
	this.cache = cache;
        getLocalClass2FinalVar();
    }
    
    /** 
     * returns the default value of the given type 
     * according to JLS Sect. 4.5.5
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
     */
    public Expression getDefaultValue(Type type) {
	if (type instanceof ClassType || type instanceof ArrayType) {
	    return new NullLiteral();
	} else if (type instanceof PrimitiveType) {
	    if ("boolean".equals(type.getName())) {
		return new BooleanLiteral(false);
	    } else if ("byte".equals(type.getName())  ||
		       "short".equals(type.getName()) || 
		       "int".equals(type.getName())) {
		return new IntLiteral(0);
	    } else if ("long".equals(type.getName())) {
		return new LongLiteral(0);
	    } else if ("char".equals(type.getName())) {
		return new CharLiteral((char)0);
	    } else if ("float".equals(type.getName())) {
		return new FloatLiteral(0.0F);
	    } else if ("double".equals(type.getName())) {
		return new DoubleLiteral(0.0D);
	    }
	}
	Debug.fail("makeImplicitMembersExplicit: unknown primitive type"+type);
	return null;
    }
    
    /** 
     * attaches a method declaration to the declaration of type td at
     * position idx
     * @param md the MethodDeclaration to insert
     * @param td the TypeDeclaration that becomes parent of the new
     * method
     * @param idx the position where to add the method
     */
    public void attach(MethodDeclaration md, TypeDeclaration td, 
		       int idx) {
	super.attach(md, td, idx);
    }

    /**
     * returns if changes have to be reported to the change history
     * @return true, if changes have to be reported to the change history
     */
    public boolean isVisible() {
	return true;
    }
    
    /**
     * The method is called for each type declaration of the compilation
     * unit and initiates the syntactical transformation. If you want to
     * descend in inner classes you have to implement the recursion by
     * yourself.
     */
    protected abstract void makeExplicit(TypeDeclaration td);

    // Java construction helper methods for recoder data structures

    protected FieldReference attribute
	(ReferencePrefix prefix, Identifier attributeName) {
	return new FieldReference(prefix, attributeName);
    }


    protected CopyAssignment assign(Expression lhs, Expression rhs) {
	return new CopyAssignment(lhs, rhs);
    }

    protected LocalVariableDeclaration declare
	(String name, ClassType type) {
	return new LocalVariableDeclaration
	    (new TypeReference(new Identifier(type.getName())), 
	     new Identifier(name));
    }

    protected LocalVariableDeclaration declare
	(String name, Identifier type) {
	return new LocalVariableDeclaration
	    (new TypeReference(type), 
	     new Identifier(name));
    }
    
    protected Identifier getId(TypeDeclaration td){
      /*  return td.getIdentifier()==null ? 
            new Identifier(td.getFullName()) :
                (Identifier)td.getIdentifier().deepClone();*/
        return td.getIdentifier()==null ? 
                (td.getAllSupertypes().get(1) instanceof TypeDeclaration ?
                        getId((TypeDeclaration) td.getAllSupertypes().get(1)) : 
                            new Identifier(td.getAllSupertypes().get(1).getName())) :
                    (Identifier)td.getIdentifier().deepClone();
    }
    
    protected ClassDeclaration containingClass(TypeDeclaration td){
        NonTerminalProgramElement container = (ClassDeclaration) td.getContainingClassType();
        if(container == null){
            container = td.getASTParent();
        }
        while(!(container instanceof ClassDeclaration)){
            container = container.getASTParent();
        }
        return (ClassDeclaration) container;
    }
    
    protected MethodDeclaration containingMethod(TypeDeclaration td){
        NonTerminalProgramElement container = td.getASTParent();
        while(container!=null && !(container instanceof MethodDeclaration)){
            container = container.getASTParent();
        }
        return (MethodDeclaration) container;
    }

    /**
     * invokes model transformation for each top level type declaration
     * in any compilation unit. <emph>Not</emph> for inner classes.
     */
    public void makeExplicit() {
	Set<ClassDeclaration> s = classDeclarations();
	Iterator<ClassDeclaration> it = s.iterator();
	while(it.hasNext()) {
	    ClassDeclaration cd = it.next();
  //          System.out.println("RecoderModelTransformer: classdecl: "+cd.getFullName());
            makeExplicit(cd);
        }
    }
    
    // 3 methods to access the transformation cache.
    
    protected Set<ClassDeclaration> classDeclarations(){
        return cache.getClassDeclarations();       
    }
    
    public HashMap<ClassType, List<Variable>> getLocalClass2FinalVar(){
        return cache.getLocalClass2FinalVarMapping();
     }
    
    public List<CompilationUnit> getUnits() {
        return cache.getUnits();
    }
    
 /*   protected String getNameForAnonClass(TypeDeclaration cd){
        return cd.getAllSupertypes().getClassType(1).getFullName();
    }*/

    /**
     * Starts the transformation. 
     */
    public void transform() {
	super.transform();
	makeExplicit();
    }
    
    /**
     * Cache of important data. This is done mainly for performance reasons.
     * It contains the following info:
     * - list of comp. units
     * - their class declarations
     * - a mapping from local classes to their needed final variables.
     * 
     * Objects are created upon the first request.
     *  
     * @author MU
     */
    public static class TransformerCache {
        
        private List<CompilationUnit> cUnits;
        private Set<ClassDeclaration> classDeclarations;
        private HashMap<ClassType, List<Variable>> localClass2FinalVar;

        public TransformerCache(List<CompilationUnit> cUnits) {
            this.cUnits = cUnits;    
        }
        
        public List<CompilationUnit> getUnits() {
            return cUnits;
        }
        
        public Set<ClassDeclaration> getClassDeclarations(){
            if(classDeclarations==null){
                ClassDeclarationCollector cdc = new ClassDeclarationCollector();
                for (int i = 0; i < cUnits.size(); i++) {
                CompilationUnit unit = cUnits.get(i);
                    cdc.walk(unit);
                }
                classDeclarations = cdc.result();
            }
            return classDeclarations;       
        }
        
        public HashMap<ClassType, List<Variable>> getLocalClass2FinalVarMapping() {
            if(localClass2FinalVar == null){
                localClass2FinalVar = new HashMap<ClassType, List<Variable>>();
            }
            return localClass2FinalVar;
        }

        /**
         * if the class declaration set changes, the cash must be invalidated
         */
        public void invalidateClasses() {
            classDeclarations = null;
        }
    }
    
    protected class FinalOuterVarsCollector extends SourceVisitor{
        
        HashMap<ClassType, List<Variable>> lc2fv;
        
        public FinalOuterVarsCollector(){
            super();
            lc2fv = cache.getLocalClass2FinalVarMapping();
        }
        
        public void walk(SourceElement s){
            s.accept(this);
            if(s instanceof NonTerminalProgramElement){
                NonTerminalProgramElement pe = (NonTerminalProgramElement) s;
                for(int i=0; i<pe.getChildCount(); i++){
                    walk(pe.getChildAt(i));
                }
            }
        }
        
       public void visitVariableReference(VariableReference vr){
           DefaultCrossReferenceSourceInfo si = (DefaultCrossReferenceSourceInfo) services.getSourceInfo();
           Variable v = si.getVariable(vr.getName(), vr);
           if((v instanceof VariableSpecification) && !(v instanceof FieldSpecification) &&
                   si.getContainingClassType((ProgramElement) v) != si.getContainingClassType(vr)){
               List<Variable> vars = lc2fv.get(si.getContainingClassType(vr));
               if(vars == null){
                   vars = new LinkedList<Variable>();
               }
               if(!vars.contains(v)){
                   vars.add(v);
               }
               lc2fv.put(si.getContainingClassType(vr), vars);
           }
       }
        
    }
    
    private static class ClassDeclarationCollector extends SourceVisitor{
        
        HashSet<ClassDeclaration> result = new HashSet<ClassDeclaration>();
        
        public ClassDeclarationCollector(){
            super();
        }
        
        public void walk(SourceElement s){
            s.accept(this);
            if(s instanceof NonTerminalProgramElement){
                NonTerminalProgramElement pe = (NonTerminalProgramElement) s;
                for(int i=0; i<pe.getChildCount(); i++){
                    walk(pe.getChildAt(i));
                }
            }
        }
        
        public void visitClassDeclaration(ClassDeclaration cld){
            result.add(cld);
//            System.out.println("ClassDeclarationCollector: classdecl: "+cld.getName());
            super.visitClassDeclaration(cld);
        }
               
        public HashSet<ClassDeclaration> result(){
            return result;
        }
    }

}
