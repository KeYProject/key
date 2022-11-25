package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class MethodPositioner implements InsPositionProvider {
    private final Services svc;
    private final Proof proof;
    private final Sequent sequent;

    public MethodPositioner(Services svc, Proof proof, Node node) {
        this.svc = svc;
        this.proof = proof;
        this.sequent = node.sequent();
    }

    public PositionInfo getPositionMap() throws TransformException {

        ContractPO contractPO = svc.getSpecificationRepository().getPOForProof(proof);

        if (!(contractPO instanceof FunctionalOperationContractPO)) {
            throw new TransformException("Can only work on functional contracts");
        }

        FunctionalOperationContractPO funContractPO = (FunctionalOperationContractPO) contractPO;

        FunctionalOperationContract contract = funContractPO.getContract();

        IProgramMethod progrMethod = contract.getTarget();

        PositionInfo pos = progrMethod.getPositionInfo();

        return pos;
    }

    private int getLine(InsertionTerm iterm) throws TransformException, InternTransformException {
        var methodPosition = getPositionMap();

        if (iterm.Type == InsertionType.ASSUME) {
            return methodPosition.getStartPosition().getLine() + 1;
        }
        if (iterm.Type == InsertionType.ASSUME_ERROR) {
            return methodPosition.getStartPosition().getLine() + 1;
        }
        if (iterm.Type == InsertionType.ASSERT) {
            return methodPosition.getEndPosition().getLine();
        }
        if (iterm.Type == InsertionType.ASSIGNABLE) {
            return methodPosition.getEndPosition().getLine();
        }
        if (iterm.Type == InsertionType.ASSERT_ERROR) {
            return methodPosition.getEndPosition().getLine();
        }
        throw new InternTransformException("unknown InsertionTerm.Type");

    }

    public int getLineIndent(int line) {
        return 9; // TODO
    }

    @Override
    public InsertionPosition getPosition(InsertionTerm iterm) throws TransformException, InternTransformException {

        var line = getLine(iterm);
        var indent = getLineIndent(line);

        return new InsertionPosition(line, indent);
    }
}
