package de.uka.ilkd.key.parser.jml;

import java.util.LinkedHashMap;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Model;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.jml.JMLClassSpec;
import de.uka.ilkd.key.jml.JMLNormalMethodSpec;
import de.uka.ilkd.key.jml.JMLSpec;
import de.uka.ilkd.key.jml.UsefulTools;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ArraySortImpl;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


/**
 * This class is used to decouple JML parser and JMLDL translation
 * (further refactoring needs to be done) 
 */
public class JMLTranslator extends TermBuilder {
    
    private static int            oldVarCount = 0;
    
    private final ArithOpProvider aOP;
    
    private final TypeDeclaration cld;   
    
    private KeYJMLParser    parser;
    
    private final Services        services;
    
    private final KeYJavaType cldKeYJavaType;
    
    
    private ReferencePrefix prefix;

 
    
    public JMLTranslator(TypeDeclaration cld, Services services,
            KeYJMLParser parser, ArithOpProvider aOP) {
        this.cld = cld;
        this.services = services; 
        this.aOP = aOP;           
        this.parser = parser;
        cldKeYJavaType = services.getJavaInfo().getKeYJavaType(cld);
        //this.allInt = allInt;
    }
    
    public ReferencePrefix prefix() {
        return prefix;
    }
    
    public void setPrefix(ReferencePrefix prefix) {
        this.prefix = prefix;       
    }
    
    public boolean isInterface() {
        return cld instanceof InterfaceDeclaration;
    }
    
    public KeYJavaType getCLDKeYJavaType() {
        return cldKeYJavaType;
    }

    public KeYJavaType getArrayTypeAndEnsureExistence(Sort baseSort,
                                                       int dim){
        final JavaInfo ji = getJavaInfo();
        Sort as = ArraySortImpl.getArraySortForDim(
            baseSort, dim, 
            ji.getJavaLangObjectAsSort(),
            ji.getJavaLangCloneableAsSort(),
            ji.getJavaIoSerializableAsSort());
        KeYJavaType kjt = ji.getKeYJavaType(as);
        if(kjt == null || baseSort.toString().equals("int")){
            JavaBlock jb = ji.readJavaBlock("{"+as+" v;}");
            return ((VariableDeclaration) 
                    ((StatementBlock) jb.program()).getChildAt(0)).
                        getTypeReference().getKeYJavaType();
        }
        return kjt;
    }
    
    public Term buildQuantifierTerm(String q, ListOfNamed l, Term a, Term t,
            JMLSpec currentSpec) throws NotSupportedExpressionException {
        
        checkSupportedQuantifier(q);
        
        Term body = t;        
        
        if (q.equals("\\min") || q.equals("\\max")) {
            boolean isLong = isLong(t);
            Function comp;
            Function minmax;
            ProgramVariable mv;
            String varName;
            
            if (q.equals("\\min")) {
                varName = "_min";
                minmax = aOP.getMax(isLong);
                comp = (Function) functions().lookup(new Name("leq"));
            } else {
                varName = "_max";
                minmax = aOP.getMin(isLong);
                comp = (Function) functions().lookup(new Name("geq"));
            }
            
            mv = new LocationVariable(new ProgramElementName(varName
                    + (KeYJMLParser.paramVarCount++)), services.getJavaInfo()
                    .getKeYJavaType(isLong ? "long" : "int"));
            currentSpec.getProgramVariableNS().add(mv);
            final Term mvTerm = var(mv);
            
            final Term ex1 = and(not(parser.buildQuantifierTerm("\\exists", l,
                    null, a)), equals(func(minmax), mvTerm));
            final Term ex2 = parser.buildQuantifierTerm("\\exists", l, a,
                    equals(mvTerm, t));
            
            final Term allq = parser.buildQuantifierTerm("\\forall", l, a, tf
                    .createFunctionTerm(comp, new Term[] { mvTerm, t }));
            
            return parser.createModelMethod(
                    q.substring(1) + (KeYJMLParser.mmCount++), mvTerm, null, or(ex1,
                            and(allq, ex2)));
        }
        
        if (l == SLListOfNamed.EMPTY_LIST) {
            if (a != null) {
                if (q.equals("\\exists")) {
                    body = and(a, body);
                } else {
                    body = imp(a, body);
                }
            }
            return body;
        } else {
            Quantifier op = null;
            if (q.equals("\\forall")) {
                op = Op.ALL;
            } else if (q.equals("\\exists")) {
                op = Op.EX;
            } else {
                throw new IllegalArgumentException("Quantifier " + q
                        + " not supported");
            }
            body = parser.buildQuantifierTerm(q, l.tail(), a, t);
            final LogicVariable lv = (LogicVariable) l.head();           
            
            final Term vTerm = var(lv);
            // if the quantified variables have an objecttype, we only quantify
            // over objects that are already created (nevertheless the
            // quantified variable may be null)
            if (lv.sort() instanceof ObjectSort) {
                final Term createdTerm = UsefulTools.isCreated(vTerm, services);
                
                final Term nullComp = equals(vTerm, NULL(services));
                final Term cnCond = or(and(createdTerm, not(nullComp)),
                        nullComp);
                if (op == Op.ALL) {
                    body = imp(cnCond, body);
                } else {
                    body = and(cnCond, body);
                }
            }
            return tf.createQuantifierTerm(op, lv, body);
        }
    }
    
    private void checkSupportedQuantifier(String str)
    throws NotSupportedExpressionException {
        final String[] notSupported = { "\\sum", "\\product", "\\num_of" };
        
        for (int i = 0; i < notSupported.length; i++) {
            if (str.equals(notSupported[i])) {
                throw new NotSupportedExpressionException("Quantifier " + str);
            }
        }
    }
    
    /**
     * creates a model method and adds it to the class specification
     */
    public Term createModelMethod(String name, Term result, Term pre,
            Term post, final JMLClassSpec cSpec, final boolean staticMode) {
        final ExtList el = new ExtList();
        
        ListOfTerm pvs = UsefulTools.getProgramVariablesFromTerm(result,
                SLListOfTerm.EMPTY_LIST);
        pvs = UsefulTools.getProgramVariablesFromTerm(pre, pvs);
        pvs = UsefulTools.getProgramVariablesFromTerm(post, pvs);
        
        el.add(new Public());
        if (staticMode) {
            el.add(new Static());
        } else {
            pvs = pvs.removeAll(var((ProgramVariable) parser.prefix()));
        }
        IteratorOfTerm it = pvs.iterator();
        while (it.hasNext()) {
            el.add(UsefulTools.getParameterDeclForVar(it.next(), services));
        }
        el.add(new ProgramElementName(name));
        final KeYJavaType type = services.getJavaInfo().getKeYJavaType(result.sort());
        el.add(new TypeRef(type));
        el.add(new Model());
        
        final MethodDeclaration meth = new MethodDeclaration(el, false);
        final ProgramMethod pm = new ProgramMethod(meth, getCLDKeYJavaType(), 
                type, PositionInfo.UNDEFINED);
        cSpec.addModelMethod(pm);
        final JMLNormalMethodSpec spec = new JMLNormalMethodSpec(pm, 
                services, new Namespace(), new LinkedHashMap(), cSpec, parser.namespaces(), 
                parser.javaPath());
        
        result = equals(result, var(spec.getResultVar()));
        if (pre != null) {
            spec.addPre(pre);
        }
        spec.addPost(result);
        if (post != null) {
            spec.addPost(post);
        }
        spec.setAssignableMode("nothing");
        services.getImplementation2SpecMap().addModifier(pm, "pure");
        services.getImplementation2SpecMap().addModifier(pm, "helper");
        return UsefulTools.createTermForQuery(pm, pvs, parser.prefix());
    }
    
    public TypeDeclaration cld() {
        return cld;
    }
    
    private Namespace functions() {
        return parser.functions();
    }
    
    private JavaInfo getJavaInfo() {
        return services.getJavaInfo();
    }
    
    private String getNameForOld(Term t) {
        if (t.op() instanceof ProgramVariable) {
            return ("_old" + (oldVarCount++) + "_" + (t.toString().length() > 25 ? t
                    .toString().substring(0, 25)
                    : t.toString())).replace('.', '_').replace(':', '_');
        } else {
            return ("_old" + (oldVarCount++));
        }
    }
    
    /**
     * checks if term t contains the Named object o
     * @return true if o occurs in the term and is instance of Term,
     * ProgramVariable, QuantifiableVariable, SchemaVariable or Operator.
     */
    public boolean occurCheck(Term t, Named o){
        if(t.op().equals(o) || this.equals(o)) return true;
        if(o instanceof ProgramVariable && t.javaBlock().program()!=null){
            ProgramVariableCollector collector=
                new ProgramVariableCollector(t.javaBlock().program());
            collector.start();
            if(collector.result().contains(o)) return true;
        }
        if(o instanceof QuantifiableVariable){
            if(t.freeVars().contains((QuantifiableVariable) o)) return true;
            for(int i=0;i<t.arity();i++){
                for (int j=0;j<t.varsBoundHere(i).size();j++){
                    if(t.varsBoundHere(i).getQuantifiableVariable(j).equals(o))
                        return true;
                }
            }
        }            
        for(int i=0;i<t.arity();i++){
            if(occurCheck(t.sub(i), o)) return true;
        }
        return false;
    } 
    
    public Term getOld(Term t, JMLSpec currentSpec) {
        if (t.isRigid()) return t;
        Term old = (Term) parser.term2old().get(t);
        final TypeConverter typeConverter = services.getTypeConverter();
        final Sort intSort = typeConverter.getIntegerLDT().targetSort(); 
        final Sort jintSort = typeConverter.getIntLDT().targetSort();    
        boolean allInt = Main.testMode;
        if (old == null) {
            final Term TRUE = TRUE(services);            
            ListOfNamed freeVariables = parser.variables().allElements();
            final IteratorOfNamed nit = freeVariables.iterator();
           
            while(nit.hasNext()){
                Named n = nit.next();
                if(!occurCheck(t, n)){
                    freeVariables = freeVariables.removeAll(n);
                } else {
                    final Sort varSort = ((LogicVariable) n).sort();
                    allInt = allInt && 
                        (varSort == intSort || varSort == jintSort);
                }
            }
            
            if (freeVariables.size() != 0) {
                final Sort retSort;
                if (t.sort() == Sort.FORMULA) {
                    retSort = getJavaInfo().getKeYJavaType(
			PrimitiveType.JAVA_BOOLEAN).getSort();
                } else {
                    retSort = t.sort();
                }              
                
                final Term[] args = new Term[freeVariables.size()];
                final Sort[] argSorts = new Sort[freeVariables.size()];
                final IteratorOfNamed it = freeVariables.iterator();
                for (int i = 0; it.hasNext(); i++) {                
                    args[i] = var((LogicVariable) it.next());
                    argSorts[i] = args[i].sort();                    
                }                
                if(allInt){
                    ProgramVariable oldV = new LocationVariable(
                        new ProgramElementName(getNameForOld(t)), 
                        getArrayTypeAndEnsureExistence(t.sort(), 
                            freeVariables.size())); 
                    currentSpec.getProgramVariableNS().add(oldV);
                    old = tf.createArrayTerm(ArrayOp.getArrayOp(
                            oldV.sort()), tf.createVariableTerm(oldV), args);
                } else {
		    final Function f = 
			new RigidFunction(new Name(getNameForOld(t)), 
					  retSort, argSorts);
		    currentSpec.getFunctionNS().add(f);
		    functions().add(f);
		    
		    old = func(f, args);
                }
                if (isLong(t) && aOP.getCastToLong() != null) {
                    old = func(aOP.getCastToLong(), old);
                }               
            } else {
		final ProgramVariable oldV = 
		    new LocationVariable(new ProgramElementName(
						      getNameForOld(t)), 
						getTypeForOld(t));
                currentSpec.getProgramVariableNS().add(oldV);
                old = var(oldV);                
            }
            
            if (t.sort() == Sort.FORMULA) {
                old = equals(old, TRUE);
            }            
            parser.term2old().put(t, old);
        }
        return old;
    }
    
    private KeYJavaType getTypeForOld(Term t) {
        KeYJavaType type4old;
        if (t.sort() == Sort.FORMULA) {
            type4old = getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
        } else {
            if (isLong(t)) {
                type4old = 
		    getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
            } else {
                if (t.op() instanceof ProgramVariable) {
                    type4old = ((ProgramVariable) t.op()).getKeYJavaType();
                } else {
                    type4old = getJavaInfo().getKeYJavaType(t.sort());
                }
            }
        }
	if(type4old == null){
	    type4old = getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
	}
        return type4old;
    }
    
    public boolean isLong(Term t) {
        final TypeConverter typeConverter = 
            services.getTypeConverter();
        if (t.sort() == typeConverter.getLongLDT().targetSort()) {
            return true;
        }
        
        if (t.sort() == Sort.FORMULA) {
            return false;
        }
        
        if (t.op() instanceof ProgramVariable) {
            return PrimitiveType.JAVA_LONG.equals(((ProgramVariable) t.op())
                    .getKeYJavaType().getJavaType());
        }
        
        final Function modLong = 
            typeConverter.getLongLDT().getModuloLong();
        
        if (t.op() == modLong) {
            return true;
        }
        
        for (int i = 0; i < t.arity(); i++) {
            if (isLong(t.sub(i))) {
                return true;
            }
        }
        return false;
    }
    
    
    /**
     * returns the translation of \\nonnullelements(t).
     */
    protected Term nonNullElements(Term t, JMLSpec currentSpec) {
        Term nne, body;
        
        Term eq1 = not(equals(t, NULL(services)));
        
        if (t.sort() instanceof ArraySort
                && ((ArraySort) t.sort()).elementSort() instanceof ObjectSort) {
            final ProgramVariable v = new LocationVariable(
                    new ProgramElementName("_idx" + KeYJMLParser.paramVarCount),
                    services.getJavaInfo().getKeYJavaType("int"));
            currentSpec.getProgramVariableNS().add(v);
            
            
            final Term vTerm = var(v);                        
            
            final LogicVariable lv = new LogicVariable(new Name("index_lv"
                    + (KeYJMLParser.paramVarCount++)), 
                    services.getTypeConverter().getIntegerLDT().targetSort());
            
            // eq2 = tf.createEqualityTerm(vTerm, tf.createVariableTerm(lv));
            final ProgramVariable length = services.getJavaInfo().getAttribute(
                    "length", (ObjectSort) t.sort());
            
            body = and(leq(zero(services), vTerm, services), 
                        lt(vTerm, dot(t, length),  services));
            
            // body = tf.createJunctorTerm(Op.IMP, new Term[]{eq2, body});
            nne = nonNullElements(array(t, vTerm), currentSpec);
            
            eq1 = and(eq1, all(lv, 
                               tf.createUpdateTerm(vTerm, var(lv), imp(body, nne))));
        }
        return eq1;
    }
    
}
