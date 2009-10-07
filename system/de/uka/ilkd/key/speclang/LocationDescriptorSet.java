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
