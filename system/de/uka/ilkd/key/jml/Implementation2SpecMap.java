// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.jml;

import java.util.*;

import de.uka.ilkd.key.collection.SetAsListOfString;
import de.uka.ilkd.key.collection.SetOfString;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.java.annotation.LoopInvariantAnnotation;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class Implementation2SpecMap{
    
    //maps method declarations to a set of method specifications.
    private HashMap method2specs;
    //maps class or interface declarations to a class specification.
    private TreeMap class2spec;
    private HashMap loop2spec;
    private HashMap method2JMLModifiers;
    private Services services;
    //used for caching inherited methodspecs
    private HashMap inheritedSpecCache;

    private Term allInv = null;
    // Namespace containing all program variables occuring in allInv
    private Namespace allInvNS = null;

    public Implementation2SpecMap(Services services){
	method2specs = new HashMap();
	class2spec = new TreeMap(new TypeComparator());
	method2JMLModifiers = new HashMap();
	this.services = services;
	inheritedSpecCache = new HashMap();
	loop2spec = new HashMap();
    }

    private Implementation2SpecMap(HashMap method2specs, TreeMap class2spec,
				   HashMap method2JMLModifiers,
				   HashMap inheritedSpecCache, 
				   HashMap loop2spec,
				   Services services){
	this.method2specs = method2specs;
	this.class2spec = class2spec;
	this.method2JMLModifiers = method2JMLModifiers;
	this.inheritedSpecCache = inheritedSpecCache;
	this.loop2spec = loop2spec;
	this.services = services;
    }

    public void addMethodSpec(JMLMethodSpec ms){
	if(method2specs.get(ms.getProgramMethod()) == null){
	    ms.setId(0);
	    method2specs.put(ms.getProgramMethod(), 
			     SetAsListOfJMLMethodSpec.EMPTY_SET.add(ms));
	}else{
	    SetOfJMLMethodSpec specs = (SetOfJMLMethodSpec) method2specs.
		get(ms.getProgramMethod());
	    ms.setId(specs.size());
	    method2specs.put(ms.getProgramMethod(), specs.add(ms));
	}
    }

    public void addAllMethodSpecs(Set set){
	Iterator it = set.iterator();
	while(it.hasNext()){
	    addMethodSpec((JMLMethodSpec) it.next());
	}
    }

    public void setAllInvariants(Term inv){
	allInv = inv;
    }

    /**
     * returns the conjunction of all existing class invariants.
     */
    public Term allInvariants(){
	return allInv;
    }

    public void setAllInvPVNS(Namespace ns){
	allInvNS = ns;
    }

    public Namespace getAllInvPVNS(){
	return allInvNS;
    }

    public SetOfJMLMethodSpec getSpecsForMethod(ProgramMethod md){
	return (SetOfJMLMethodSpec) method2specs.get(md);
    }

    /**
     * Removes the specifications for <code>md</code>.
     */
    public void clearSpecsForMethod(ProgramMethod md){
	method2specs.remove(md);
    }

    public void addModifier(ProgramMethod md, String modifier){
	if(method2JMLModifiers.get(md) == null){
	    method2JMLModifiers.put(md, SetAsListOfString.EMPTY_SET.add(
					modifier));
	}else{
	    method2JMLModifiers.put(
		md,((SetAsListOfString) method2JMLModifiers.get(md)).
		add(modifier));
	}
    }

    public void addLoopSpec(LoopInvariant l){
	loop2spec.put(l.getLoop(), l);
    }

    public void clearSpecsForLoop(LoopStatement ls){
	loop2spec.remove(ls);
    }

    public LoopInvariant getSpecForLoop(LoopStatement ls){
	return (LoopInvariant) loop2spec.get(ls);
    }

    /**
     * Creates LoopInvariantAnnotations from the parsed loop specifications and
     * adds them to the correcponding loop statements.
     */
    public void createLoopAnnotations(){
	Iterator it = loop2spec.keySet().iterator();
	while(it.hasNext()){
	    LoopStatement loop = (LoopStatement) it.next();
	    LoopInvariant li = (LoopInvariant) loop2spec.get(loop);
	    SetOfLocationDescriptor assignable;
	    if("nothing".equals(li.getAssignableMode())){
		assignable = SetAsListOfLocationDescriptor.EMPTY_SET;
	    }else if("everything".equals(li.getAssignableMode())){
		assignable = SetAsListOfLocationDescriptor.EMPTY_SET.add(
                                    EverythingLocationDescriptor.INSTANCE);
	    }else{
		assignable = li.getAssignable();
	    }
	    Term[] olds = new Term[2*li.getTerm2Old().size()];
	    Iterator kit = li.getTerm2Old().keySet().iterator();
	    int i = 0;
	    while(kit.hasNext()){
		Term t = (Term) kit.next();
		olds[i++] = t;
		olds[i++] = (Term) li.getTerm2Old().get(t);
	    }
	    loop.addLoopInvariant(new LoopInvariantAnnotation(
				      li.getInvariant(), assignable, 
				      new ArrayOfTerm(olds), li.getVariant(),
				      li.getPost(), li.getSelfVar()));
	}
    }
 
    /**
     * adds the pure-modifier to every constructor and instance method declared
     * in <code>kjt</code>
     */
    public void setPure(KeYJavaType kjt, NamespaceSet nss, String javaPath){
	ListOfProgramMethod l = services.getJavaInfo().getAllProgramMethods(kjt);
	IteratorOfProgramMethod it = l.iterator();
	ProgramMethod md;
	while(it.hasNext()){
	    md = it.next();
	    if(!md.isStatic()){
                new JMLPuritySpec(md, services, 
				  UsefulTools.buildParamNamespace(md.getMethodDeclaration()), 
                                  new LinkedHashMap(), getSpecForClass(kjt), nss, javaPath); 
                //%% How get the java path here???
		addModifier(md, "pure");
	    }
	}
    }

    /**
     * returns a list of KeYJavaTypes, that contain a specification for the
     * method with the name <code>name</code>, in depth first order.
     */
    public ListOfKeYJavaType findSpecifications(String name, 
						KeYJavaType classType){
	ListOfKeYJavaType types = findSpecificationsInSubT(name, classType);
	types = types.append(findSpecificationsInSuperT(name, classType));
	return types;
    }

    private ListOfKeYJavaType findSpecificationsInSubT(String name, 
						       KeYJavaType classType) {
	ListOfKeYJavaType types = SLListOfKeYJavaType.EMPTY_LIST;
	JMLClassSpec cSpec      = getSpecForClass(classType);
	//	TypeDeclaration td = cSpec.getClassDeclaration();	
        // %%RB are here all subtypes needed or only the direct ones
        ListOfKeYJavaType subtypes = 
	    services.getJavaInfo().getAllSubtypes(classType);
	if(cSpec != null && cSpec.lookupModelMethodLocally(name) != null){
	    types = types.prepend(classType);
	}
	IteratorOfKeYJavaType it = subtypes.iterator();
	while(it.hasNext()){
	    types = types.prepend(findSpecificationsInSubT(name, it.next()));
	}
	return types;
    }

    private ListOfKeYJavaType findSpecificationsInSuperT(String name, 
							 KeYJavaType classType){
	ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST;
	ListOfKeYJavaType sts = 
	    ((TypeDeclaration) classType.getJavaType()).getSupertypes();
	IteratorOfKeYJavaType it = sts.iterator();
	while(it.hasNext()){
	    KeYJavaType current = it.next();
	    JMLClassSpec cSpec = getSpecForClass(current);
	    if(cSpec != null && cSpec.lookupModelMethodLocally(name) != null){
		return result.append(current);
	    }else{
		result = findSpecificationsInSuperT(name, current);
		if(result != SLListOfKeYJavaType.EMPTY_LIST){
		    return result;
		}
	    }	    
	}
	return SLListOfKeYJavaType.EMPTY_LIST;
    }

    /**
     * returns the method <code>methodName</code> if such a method is declared
     * in <code>classType</code>, null otherwise.
     */
    public ProgramMethod lookupModelMethod(KeYJavaType classType, 
					   Name methodName){
	JMLClassSpec spec = getSpecForClass(classType);
	ProgramMethod pm = null;
	if(spec != null){
	    try{
		pm = spec.lookupModelMethod(methodName);
	    }catch(AmbigiousModelElementException e){
		System.err.println(e.toString());
	    }
	}
    	return pm;
    }


    /**
     * returns the field <code>fieldName</code> if such an attribute is
     * declared in <code>classType</code>, null otherwise.
     */
    public ProgramVariable lookupModelField(KeYJavaType classType, 
					  String fieldName){
	JMLClassSpec spec = getSpecForClass(classType);
	ProgramVariable v = null;
	if(spec != null){
	    try{
		v = spec.lookupModelField(new Name(fieldName));
	    }catch(AmbigiousModelElementException e){
		System.err.println(e.toString());
	    }
	}
    	return v;
    }

    public SetOfString getModifiers(ProgramMethod md){
	if(method2JMLModifiers.get(md) != null){
	    return (SetOfString) method2JMLModifiers.get(md);
	}else{
	    return SetAsListOfString.EMPTY_SET;
	}
    }

    /** checks whether the methods annotated with the pureModifier really
     * have no side effect. This is done by allowing only normal_behavior
     * specs with \nothing as assignable clause which is slightly different
     * to jml definition of purity which allows the possibility of throwing
     * exceptions.
     */
/*    public void checkPurity(){
	Iterator it = method2JMLModifiers.keySet().iterator();
	while(it.hasNext()){
	    MethodDeclaration md = (MethodDeclaration) it.next();
	    SetOfString set = (SetOfString) method2JMLModifiers.get(md);
	    if(set.contains("pure")){
		SetOfJMLMethodSpec specs = getSpecsForMethod(md);
		if(specs != null){
		    IteratorOfJMLMethodSpec spit = specs.iterator();
		    while(spit.hasNext()){
			JMLMethodSpec spec = spit.next();
			if(!(spec instanceof JMLNormalMethodSpec)){
			    JOptionPane.showConfirmDialog
				(null,
				 "One of your specification cases for the "+
				 "pure method\n"+md.getName()+
				 "\nis not a normal_behavior specification case", 
				 "Warning",
				 JOptionPane.DEFAULT_OPTION,
				 JOptionPane.WARNING_MESSAGE);
			}
			if(!spec.terminates()){
			    JOptionPane.showConfirmDialog
				(null,
				 "Your specification for the pure method\n"+
				 md.getName()+
				 "\nallows nontermination", 
				 "Warning",
				 JOptionPane.DEFAULT_OPTION,
				 JOptionPane.WARNING_MESSAGE);
			}			    
			if(!(md instanceof ConstructorDeclaration)){
			    if(!"nothing".equals(spec.getAssignableMode())){
				JOptionPane.showConfirmDialog
				    (null,
				     "Pure Methods may not"+
				     " assign to any fields. "+
				     "\nplease check your specifications for "+
				     md.getName(), 
				     "Inconsistent Specification",
				     JOptionPane.DEFAULT_OPTION,
				     JOptionPane.WARNING_MESSAGE);
			    }
			}else{
			    IteratorOfTerm itt = 
				spec.getAssignable().iterator();
			    while(itt.hasNext()){
				checkStatic(itt.next(), md);
			    }
			}
		    }
		}
	    }
	}
    }

    private void checkStatic(Term t, MethodDeclaration md){
	if(t.op() instanceof ProgramVariable &&
	   !((ProgramVariable) t.op()).isStatic()){
	    JOptionPane.showConfirmDialog
		(null,
		 "Pure Constructors may only"+
		 " assign to static fields. "+
		 "\nthat's why "+
		 md.getName()+" can't be declared pure",
		 "Inconsistent Specification", 
		 JOptionPane.DEFAULT_OPTION,
		 JOptionPane.WARNING_MESSAGE);
	}
	if(t.op() instanceof AttributeOp){
	    checkStatic(t.sub(0), md);
	}
	if(t.op() instanceof ArrayOp){
	    checkStatic(t.sub(0), md);
	    checkStatic(t.sub(1), md);
	}
    }
*/

    public void addClassSpec(JMLClassSpec cs){
	class2spec.put(services.getJavaInfo().
		       getKeYJavaType(cs.getClassDeclaration()), cs);
    }

    public JMLClassSpec getSpecForClass(KeYJavaType classType){
	return (JMLClassSpec) class2spec.get(classType);
    }

    public void removeMethodSpec(JMLMethodSpec ms){
	if(method2specs.get(ms.getProgramMethod()) != null){
	    method2specs.put(ms.getProgramMethod(),
			     ((SetOfJMLMethodSpec) method2specs.
			      get(ms.getProgramMethod())).remove(ms));
	}
    }

    public void removeClassSpec(JMLClassSpec cs){
	class2spec.remove(services.getJavaInfo().
			  getKeYJavaType(cs.getClassDeclaration()));
    }

    public Implementation2SpecMap copy(Services serv){
	Implementation2SpecMap ism = 
	    new Implementation2SpecMap((HashMap)method2specs.clone(), 
				       (TreeMap)class2spec.clone(),
				       (HashMap)method2JMLModifiers.clone(),
				       (HashMap)inheritedSpecCache.clone(),
				       (HashMap)loop2spec.clone(),
				       serv);
	//	ism.setProgVarNS(getProgVarNS());
	return ism;
    }

    public boolean equals(Object o){
	if(!(o instanceof Implementation2SpecMap)){
	    return false;
	}
	Implementation2SpecMap ism = (Implementation2SpecMap) o;
	return ism.method2specs.equals(method2specs) && ism.class2spec.
	    equals(class2spec) && ism.loop2spec.equals(loop2spec);
    }

    public int hashCode(){
	return method2specs.hashCode() + 5*class2spec.hashCode() + 
	    17*loop2spec.hashCode();
    }

    /**
     * returns all methoddeclarations in this map.
     */
    public Set getAllMethods(){
	return method2specs.keySet();
    }

    /**
     * returns all classtypes in this map.
     */
    public Set getAllClasses(){
	return class2spec.keySet();
    }

    public SetOfJMLMethodSpec getInheritedMethodSpecs(ProgramMethod md,
						      KeYJavaType classType){
	InhKey key = new InhKey(md, classType);
	if(inheritedSpecCache.get(key) != null){
	    return (SetOfJMLMethodSpec) inheritedSpecCache.get(key);
	}
	SetOfJMLMethodSpec inh = SetAsListOfJMLMethodSpec.EMPTY_SET;
	if(classType.getJavaType() instanceof InterfaceDeclaration ||
	   /*"equals".equals(md.getName()) ||*/ "finalize".equals(md.getName()) ||
	    "wait".equals(md.getName()) || "getClass".equals(md.getName())){
	    return inh;
	}
	ListOfKeYJavaType st = 
	    services.getJavaInfo().getAllSupertypes(classType);
	IteratorOfKeYJavaType it = st.iterator();
	ListOfKeYJavaType alreadyVisited = SLListOfKeYJavaType.EMPTY_LIST;
	alreadyVisited = alreadyVisited.append(classType);
	while(it.hasNext()){
	    KeYJavaType current = it.next();
	    if(alreadyVisited.contains(current)){
		continue;
	    }else{
		alreadyVisited = alreadyVisited.append(current);
	    }
	    ListOfProgramMethod l = 
		services.getJavaInfo().getAllProgramMethods(current);
	    IteratorOfProgramMethod pmIt = l.iterator();
	    while(pmIt.hasNext()){
		SetOfJMLMethodSpec specs = getSpecsForMethod(pmIt.next());
		if(specs != null){
		    IteratorOfJMLMethodSpec sIt = specs.iterator();
		    while(sIt.hasNext()){
			JMLMethodSpec spec = sIt.next();
			if(!(spec instanceof JMLPuritySpec) && 
			   spec.isCloneableFor(md) &&
			   getSpecForClass(classType) != null &&
			   spec.getInheritedPrefix() == null){
			    inh = inh.add(spec.cloneFor(md, 
					   getSpecForClass(classType)));
			}else if(!spec.isCloneableFor(md)){
			    break;
			}
		    }
		}
	    }
	}
	inheritedSpecCache.put(key, inh);
	return inh;
    }

    final static class TypeComparator implements Comparator {

	public int compare(Object o1, Object o2) {
	    final KeYJavaType type1 = (KeYJavaType) o1; 
	    final KeYJavaType type2 = (KeYJavaType) o2;
	    // attention this is only sane as long as types 
	    // are uniquely identified by their name 
	    return type1.getFullName().compareTo(type2.getFullName());	    
	}
    } 

    private static class InhKey{

	protected ProgramMethod md;
	protected KeYJavaType ct;

	public InhKey(ProgramMethod md, KeYJavaType ct){
	    this.md = md;
	    this.ct = ct;
	}

	public boolean equals(Object o){
	    if(!(o instanceof InhKey)) return false;
	    return ((InhKey) o).md == md && ((InhKey) o).ct == ct;
	}

	public int hashCode(){
	    return md.hashCode() + 31*ct.hashCode();
	}
    }
}
