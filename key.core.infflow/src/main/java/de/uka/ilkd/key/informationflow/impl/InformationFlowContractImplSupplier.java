package de.uka.ilkd.key.informationflow.impl;

import de.uka.ilkd.key.speclang.infflow.InformationFlowContract;
import de.uka.ilkd.key.speclang.infflow.InformationFlowContractInfo;
import de.uka.ilkd.key.speclang.infflow.InformationFlowContractSupplier;

public class InformationFlowContractImplSupplier implements InformationFlowContractSupplier {
    @Override
    public InformationFlowContract create(InformationFlowContractInfo info) {
        return new InformationFlowContractImpl(
                info.informationFlowContractBasename(),
                info.forClass(),
                info.pm(),
                info.specifiedIn(),
                info.modalityKind(),
                info.requires(),
                info.requiresFree(),
                info.measuredBy(),
                info.modifiable(),
                info.hasModifiable(),
                info.self(),
                info.params(),
                info.result(),
                info.exc(),
                info.atPre(),
                info.accessible(),
                info.infFlowSpecs(),
                info.toBeSaved()
        );
    }
}
