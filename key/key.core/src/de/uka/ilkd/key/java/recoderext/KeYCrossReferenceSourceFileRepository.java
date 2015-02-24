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

package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.util.SpecDataLocation;
import recoder.ServiceConfiguration;
import recoder.io.*;
import recoder.java.CompilationUnit;

/**
 * This class is used to handle source files within recoder.
 * 
 * It does only overwrite one method: createDataLocation.
 * 
 * The original method in {@link DefaultSourceFileRepository} creates references
 * to possibly non-existing files which we do not want. Thus, we leave the location
 * already present.
 * 
 * @author MU
 * 
 */

public class KeYCrossReferenceSourceFileRepository extends
        DefaultSourceFileRepository {

    public KeYCrossReferenceSourceFileRepository(ServiceConfiguration config) {
        super(config);
    }

    /**
     * return the data location that is already stored in the compilation unit.
     * If there is no location stored so far, create a temporary invalid one.
     * 
     * The super class would have created a location that does not represent the
     * existing sources.
     * 
     * @param cu
     *                Compilation unit to create the location for.
     * @return location(cu) == null ? {@link SpecDataLocation#UNKNOWN_LOCATION} :
     *         location(cu)
     */
    protected DataLocation createDataLocation(CompilationUnit cu) {
        DataLocation dataLocation = cu.getDataLocation();
        if (dataLocation == null)
            dataLocation = SpecDataLocation.UNKNOWN_LOCATION;
        return dataLocation;
    }

}