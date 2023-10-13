/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.ServiceConfiguration;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.java.Reference;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.service.KeYCrossReferenceSourceInfo;

public class SchemaCrossReferenceSourceInfo extends KeYCrossReferenceSourceInfo {

    protected final PrimitiveType recoderTypeSVType;

    public SchemaCrossReferenceSourceInfo(ServiceConfiguration config) {
        super(config);
        recoderTypeSVType = new PrimitiveType("TypeSV", this);
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        cfg.getChangeHistory().removeChangeHistoryListener(this);
    }

    public Type getType(TypeReference tr) {
        if (tr instanceof TypeSVWrapper) {
            return recoderTypeSVType;
        } else {
            return super.getType(tr);
        }
    }

    public Type getType(VariableSpecification vs) {
        if (vs.getExpressionCount() > 0
                && vs.getExpressionAt(0) instanceof ProgramVariableSVWrapper) {
            return recoderTypeSVType;
        } else {
            return super.getType(vs);
        }
    }

    /**
     * does not resolve the urq, just returns the argument
     */
    public Reference resolveURQ(UncollatedReferenceQualifier urq) {
        return urq;
    }


}
