// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;


import java.util.HashMap;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.util.Debug;



public class TestKeYRecoderMapping extends TestCase{

    private HashMap map, revmap;
    private recoder.java.ProgramElement rp,rp2;
    private ProgramElement kp;
    private recoder.ModelElement rm, rm2;
    private ModelElement km;
    private KeYRecoderMapping mapping;



    public TestKeYRecoderMapping(String name){
        super(name);
    }


    public void setUp(){
        map = new HashMap();
        revmap = new HashMap();
        rp = new recoder.java.declaration.ClassDeclaration();
        kp = (ProgramElement)(new EmptyStatement());
        rm = new recoder.java.statement.Case();
        km = (ModelElement)(new de.uka.ilkd.key.java.abstraction.Package("Packet"));
        rp2 = new recoder.java.declaration.ClassDeclaration();
        rm2 = new recoder.java.statement.Case();
        map.put(rp,kp);
        revmap.put(kp,rp);
        map.put(rm,km);
        revmap.put(km,rm);
        mapping = new KeYRecoderMapping(map, revmap, null, false);
    }
    

    public void testtoKeY(){
        Debug.assertTrue(kp.equals(mapping.toKeY(rp)),"Fehler[1] in toKeY(recoder.java.ProgramElement)");
        Debug.assertTrue(null==mapping.toKeY(rp2),"Fehler[2] in toKeY(recoder.java.ProgramElement)");
        Debug.assertTrue(km.equals(mapping.toKeY(rm)),"Fehler[3] in toKeY(recoder.ModelElement)");
        Debug.assertTrue(null==mapping.toKeY(rm2),"Fehler[4] in toKeY(recoder.ModelElement)");
    }




    public void testtoRecoder(){
        Debug.assertTrue(rp.equals(mapping.toRecoder(kp)),"Fehler[1] in toRecoder(de.uka.ilkd.key.java.ProgramElement)");
//        Debug.assertTrue(null==mapping.toRecoder(kp2),"Fehler[2] in toRecoder(de.uka.ilkd.key.java.ProgramElement)");
        Debug.assertTrue(rm.equals(mapping.toRecoder(km)),"Fehler[2] in toRecoder(de.uka.ilkd.key.java.ModelElement)");
//        Debug.assertTrue(null==mapping.toRecoder(km2),"Fehler[4] in toRecoder(de.uka.ilkd.key.java.ModelElement)");
    }


}
