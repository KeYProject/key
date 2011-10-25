// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;


import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.ExtList;

/** this class is an example how to work with a java AST. Therefore we
* demonstrate the transformation of 'while (expr) { prg; }' to ' if
* (expr) then { prg; } while (expr) { prg }'
*/

public class RecoderExample {



    /** this method is used to create the part of the AST representing
     * an if-then statement. 
     * @param expr the Expression that is the condition of the if part
     * @param prg the JavaStatement after 'then' 
     * @return the If Statement with condition expr and 'then' part prg
     */
    public If createIfThen(Expression expr, JavaStatement prg) {
	// create Then statement
	Then _then=new Then(prg);
	// create if part
	return new If(expr, _then);
    }  

    /** transformates a "while(expr) {prg;}" to "if (exr) then {prg;}"
     * @param _while the while-loop to transform
     * @return the transformed AST
     */
    public ExtList transform(While _while) {
	ExtList stmnt=new ExtList();
	stmnt.add(createIfThen(
	    ((Guard)_while.getGuard()).getExpression(), 
	    (JavaStatement)_while.getBody()));
	stmnt.add(_while);
	return stmnt;
    }


    /** transforms all while statements in a statement block to the wanted
     * "if-then-while" statement
     * @param prg the Statementblock to be transformed
     */
    public StatementBlock transform(StatementBlock prg) {
	ExtList newBody=new ExtList();
	
	ImmutableArray<? extends Statement> body=prg.getBody();
	for (int i=0;i<body.size();i++) {
	    if (body.get(i) instanceof While) {
		newBody.addAll(transform((While)body.get(i)));
	    } else {
		newBody.add(body.get(i));	    
	    }
	}
	return new StatementBlock(newBody);	
    }

    
    /** test */
    public static void main(String[] args) {
	System.out.println("Starting...");
	RecoderExample ex=new RecoderExample();
	Recoder2KeY c2k=new Recoder2KeY(TacletForTests.services(), 
	                                new NamespaceSet());
	String prg="{ int i=0; while (i<5) { i++;} }";
	JavaBlock block=c2k.readBlock(prg,c2k.createEmptyContext());
	System.out.println("Read Original:\n"+block);
	System.out.println("Transforming...");
	System.out.println("Transformed:\n"+(JavaBlock.createJavaBlock(
            ex.transform((StatementBlock)block.program()))));
	System.out.println("The original is left untouched:\n"+block);		
    }

}
