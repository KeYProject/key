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

import java.util.ArrayList;
import java.util.List;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import org.slf4j.LoggerFactory;


/**
 * Simple exception handler which just writes to standard output.
 *
 * @author bruns
 */
public class SimpleRIFLExceptionHandler extends KeYRecoderExcHandler {
    static final SimpleRIFLExceptionHandler INSTANCE = new SimpleRIFLExceptionHandler();

    @Override
    public void clear() {}

    @Override
    public List<Throwable> getExceptions() {
        return new ArrayList<>(0);
    }

    @Override
    public void reportException(Throwable e) {
        LoggerFactory.getLogger(SimpleRIFLExceptionHandler.class)
                        .error("Error occured!", e);
    }
}