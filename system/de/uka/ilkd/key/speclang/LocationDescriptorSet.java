// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.LocationDescriptor;

public class LocationDescriptorSet {

    private final ImmutableSet<LocationDescriptor> replaceLoc;

    public LocationDescriptorSet(ImmutableSet<LocationDescriptor> replaceLoc) {
	this.replaceLoc = replaceLoc;
    }

    public ImmutableSet<LocationDescriptor> asSet() {
	return replaceLoc;
    }

    public LocationDescriptor[] toArray() {
	return replaceLoc.toArray(new LocationDescriptor[replaceLoc.size()]);
    }

}
