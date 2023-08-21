/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// TODO javaparser
// package de.uka.ilkd.key.java;
//
// import java.util.HashMap;
//
// import de.uka.ilkd.key.java.statement.EmptyStatement;
//
// import com.github.javaparser.ast.Node;
// import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
// import org.junit.jupiter.api.BeforeEach;
// import org.junit.jupiter.api.Test;
//
// import static org.junit.jupiter.api.Assertions.assertEquals;
// import static org.junit.jupiter.api.Assertions.assertNull;
//
// public class TestKeYRecoderMapping {
//
// private Node rp, rp2;
// private ProgramElement kp;
// private recoder.ModelElement rm, rm2;
// private ModelElement km;
// private KeYJPMapping mapping;
//
//
// @BeforeEach
// public void setUp() {
// HashMap<Object, Object> map = new HashMap<>();
// HashMap<Object, Object> revmap = new HashMap<>();
// rp = new ClassOrInterfaceDeclaration();
// kp = new EmptyStatement();
// rm = new recoder.java.statement.Case();
// km = new de.uka.ilkd.key.java.abstraction.Package("Packet");
// rp2 = new recoder.java.declaration.ClassDeclaration();
// rm2 = new recoder.java.statement.Case();
// map.put(rp, kp);
// revmap.put(kp, rp);
// map.put(rm, km);
// revmap.put(km, rm);
// mapping = new KeYJPMapping(map, revmap, null, false);
// }
//
//
// @Test
// public void testtoKeY() {
// assertEquals(kp, mapping.toKeY(rp), "Fehler[1] in toKeY(recoder.java.ProgramElement)");
// assertNull(mapping.toKeY(rp2), "Fehler[2] in toKeY(recoder.java.ProgramElement)");
// assertEquals(km, mapping.toKeY(rm), "Fehler[3] in toKeY(recoder.ModelElement)");
// assertNull(mapping.toKeY(rm2), "Fehler[4] in toKeY(recoder.ModelElement)");
// }
//
//
//
// @Test
// public void testtoRecoder() {
// assertEquals(rp, mapping.toRecoder(kp),
// "Fehler[1] in toRecoder(de.uka.ilkd.key.java.ast.ProgramElement)");
// // Assert.assertTrue("Fehler[2] in toRecoder(de.uka.ilkd.key.java.ast.ProgramElement)",
// // null==mapping.toRecoder(kp2));
// assertEquals(rm, mapping.toRecoder(km),
// "Fehler[2] in toRecoder(de.uka.ilkd.key.java.ast.ModelElement)");
// // Assert.assertTrue("Fehler[4] in toRecoder(de.uka.ilkd.key.java.ast.ModelElement)",
// // null==mapping.toRecoder(km2));
// }
//
//
// }
