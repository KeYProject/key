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

package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;

public class DLEmbeddedExpression extends Operator {

    private final Function functionSymbol;

    /**
     * @return the functionSymbol
     */
    public Function getFunctionSymbol() {
        return functionSymbol;
    }

    public DLEmbeddedExpression(Function f, ExtList children) {
        super(children);
        this.functionSymbol = f;
    }

    /**
     * Arity of an embedded JavaDL Expression depends upon the number of
     * arguments.
     * 
     * Since the first argument may be implicitly given, we cannot use the arity
     * of {@link #functionSymbol}.
     */
    @Override
    public int getArity() {
        // return functionSymbol.arity();
        return children.size();
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.expression.Operator#getKeYJavaType(de.uka.ilkd.key.java.Services, de.uka.ilkd.key.java.reference.ExecutionContext)
     */
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        
        Sort sort = functionSymbol.sort();
        
        KeYJavaType kjt = getKeYJavaType(javaServ, sort);
        if(kjt != null) {
            return kjt;
        } else {
            // FIXME FIXME FIXME Unknown types are mapped to int.
            return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
        }
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnDLEmbeddedExpression(this);
    }
    
    @Override    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDLEmbeddedExpression(this);
    }

    public void check(Services javaServ, 
		      KeYJavaType containingClass) throws ConvertException {
        
        if(functionSymbol == null)
            throw new ConvertException("null function symbol");
        
        int expected = functionSymbol.arity();
        int actual = children.size();
        // if the first argument is the implicit heap argument, then shift everything
        // by one
        int implicitOffset = 0;
        
        if (actual == expected - 1 && 
                functionSymbol.argSort(0) == getHeapSort(javaServ)) {
            implicitOffset = 1;
        }
        
        if (expected != actual + implicitOffset) {
            throw new ConvertException("Function symbol " + functionSymbol
                    + " requires " + expected
                    + " arguments, but received only " + actual);
        }

        String name = containingClass.getSort().name().toString();	    
        String qualifier = name.lastIndexOf('.') != -1 ? name.substring(0, name.lastIndexOf('.')) : "";
        name = name.substring(name.lastIndexOf('.')+1);
        TypeRef tr = 
        		new TypeRef(new ProgramElementName(name, qualifier), 0, null, containingClass);
        ExecutionContext ec = new ExecutionContext(tr, null, null);

        for (int i = 0; i < actual; i++) {
            Sort argSort = functionSymbol.argSort(i + implicitOffset);
            KeYJavaType kjtExpected = getKeYJavaType(javaServ, argSort);
                
            Expression child = children.get(i);


            KeYJavaType kjtActual = javaServ.getTypeConverter().getKeYJavaType(child, ec);
            
            if(kjtExpected != null && !kjtActual.getSort().extendsTrans(kjtExpected.getSort())) {
                throw new ConvertException("Received " + child
                        + " as argument " + i + " for function "
                        + functionSymbol + ". Was expecting type "
                        + kjtExpected + ", but received " + kjtActual);
            }
        }
    }


    private static Sort getHeapSort(Services javaServ) {
        return javaServ.getTypeConverter().getHeapLDT().targetSort();
    }

    private static KeYJavaType getKeYJavaType(Services javaServ, Sort argSort) {
        // JavaInfo returns wrong data for sort integer! We need to find it over
        // other paths.
        JavaInfo javaInfo = javaServ.getJavaInfo();
        KeYJavaType intType = javaInfo.getPrimitiveKeYJavaType("int");
        if(argSort == intType.getSort()) {
            return intType;
        } else {
            return javaInfo.getKeYJavaType(argSort);
        }
    }

    public Term makeTerm(LocationVariable heap, Term[] subs, Services services) {
        Function f = getFunctionSymbol();
        // we silently assume that check has been called earlier

        if(f.arity() == subs.length) {
            return services.getTermFactory().createTerm(f, subs); 
        } else {
            Term[] extSubs = new Term[subs.length + 1];
            System.arraycopy(subs, 0, extSubs, 1, subs.length);
            extSubs[0] = services.getTermBuilder().var(heap);
            return services.getTermFactory().createTerm(f, extSubs);
        }
    }
}