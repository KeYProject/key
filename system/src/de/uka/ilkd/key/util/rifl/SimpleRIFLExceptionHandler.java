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

package de.uka.ilkd.key.util.rifl;

import java.util.List;

import de.uka.ilkd.key.util.KeYExceptionHandler;

/** Simple exception handler which just writes to standard output. 
 * @author bruns 
 */
public class SimpleRIFLExceptionHandler implements KeYExceptionHandler {
    
    static final SimpleRIFLExceptionHandler INSTANCE = 
            new SimpleRIFLExceptionHandler();

    private SimpleRIFLExceptionHandler() {
        // TODO Auto-generated constructor stub
    }

    @Override
    public void reportException(Throwable e) {
        System.out.println(e.toString());
        if (e.getCause() != null) {
            reportException(e.getCause());
        }
    }

    @Override
    public List<Throwable> getExceptions() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void clear() {
        // TODO Auto-generated method stub

    }

}
