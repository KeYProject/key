// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.removegenerics;

import java.util.regex.Pattern;

import junit.framework.TestCase;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.java.CompilationUnit;

public class ResolveGenericClassTest extends TestCase {
    
    protected CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();

    public CompilationUnit registerCU(String compilationUnit) throws ParserException {
        ProgramFactory f = sc.getProgramFactory();
        CompilationUnit cu = f.parseCompilationUnit(compilationUnit);
        sc.getChangeHistory().attached(cu);
        return cu;
    }

    /**
     * parse 2 comp. units transform the first and return whether the result is
     * equal to the first.
     * 
     * @param string1
     *            first comp unit as string
     * @param string2
     *            snd comp unit as string
     * @throws Exception
     */
    public void equalCU(String string1, String string2) throws Exception {
        CompilationUnit cu1 = null, cu1before = null;
        try {
            cu1 = registerCU(string1);
            cu1before = cu1.deepClone();
            
            sc.getChangeHistory().attached(cu1);
            sc.getChangeHistory().updateModel();
            
            ResolveGenerics rgc = new ResolveGenerics(sc, cu1);
            rgc.analyze();
            rgc.transform();
            
            SingleLineCommentRepairer.repairSingleLineComments(cu1);

            String diff = firstDifferentChar(cu1.toSource(), string2);

            if (diff != null) {
                throw new IllegalStateException("not equal, difference at: " + diff);
            }
        } catch (Exception ex) {
            StringBuilder sb = new StringBuilder();
            if (cu1before != null)
                sb.append("CU1 (before): " + cu1before.toSource() + "\n");
            else
                sb.append("CU1 (source): " + string1 + "\n");
            if (cu1 != null)
                sb.append("CU1 (after) : " + cu1.toSource() + "\n");
            sb.append("CU2         : " + string2 + "\n");
            throw new Exception(sb.toString(), ex);
        }
    }

    private String firstDifferentChar(String s1, String s2) {
        Pattern nospaces1 = Pattern.compile("(\\w)(\\W)");
        s1 = nospaces1.matcher(s1).replaceAll("$1 $2");
        s2 = nospaces1.matcher(s2).replaceAll("$1 $2");
        
        Pattern nospaces2 = Pattern.compile("(\\W)(\\w)");
        s1 = nospaces2.matcher(s1).replaceAll("$1 $2");
        s2 = nospaces2.matcher(s2).replaceAll("$1 $2");
        
        Pattern spaces = Pattern.compile("\\s+");
        s1 = spaces.matcher(s1).replaceAll(" ").trim();
        s2 = spaces.matcher(s2).replaceAll(" ").trim();
        
//        System.out.println("'"+s1+"'");
//        System.out.println("'"+s2+"'");

        int minlength = Math.min(s1.length(), s2.length());
        for (int i = 0; i < minlength; i++) {
            if (s1.charAt(i) != s2.charAt(i))
                return "'" + s1.substring(i, Math.min(i + 10, s1.length())) + "' vs. '" + s2.substring(i, Math.min(i + 10, s2.length()))
                        + "' @" + (i+1);
        }

        if (s1.length() != s2.length())
            return "'" + s1.substring(minlength) + "' vs. '" + s2.substring(minlength) + "' @" + (minlength+1);
        else
            return null;
    }

}