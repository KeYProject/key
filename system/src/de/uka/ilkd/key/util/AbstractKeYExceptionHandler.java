//// This file is part of KeY - Integrated Deductive Software Design
////
//// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
////                         Universitaet Koblenz-Landau, Germany
////                         Chalmers University of Technology, Sweden
//// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
////                         Technical University Darmstadt, Germany
////                         Chalmers University of Technology, Sweden
////
//// The KeY system is protected by the GNU General
//// Public License. See LICENSE.TXT for details.
////
//
//package de.uka.ilkd.key.util;
//
//import java.util.List;
//import de.uka.ilkd.key.collection.ArrayListNoDuplicates;
//
//
//public abstract class AbstractKeYExceptionHandler implements KeYExceptionHandler {
//
//    protected List<Throwable> exceptions = null;
//
//    public AbstractKeYExceptionHandler() {
//	exceptions = new ArrayListNoDuplicates<Throwable>();
//    }
//
//
//    @Override
//    public void reportException(Throwable e) {
//        exceptions.add(e);
//    }
//
//
//    @Override
//    public List<Throwable> getExceptions() {
//        return exceptions;
//    }
//
//
//    @Override
//    public void clear() {
//        exceptions.clear();
//    }
//}