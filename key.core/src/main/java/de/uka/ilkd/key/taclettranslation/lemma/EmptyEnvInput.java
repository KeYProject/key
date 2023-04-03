package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.util.Collections;

import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractEnvInput;
import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.collection.ImmutableSet;

public class EmptyEnvInput extends AbstractEnvInput {

    public EmptyEnvInput(Profile profile) {
        super("empty dummy environment", null, Collections.emptyList(), null, profile, null);
    }

    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        // nothing to to do
        return null;
    }

    @Override
    public File getInitialFile() {
        // no file availbale. may return null
        return null;
    }

}
