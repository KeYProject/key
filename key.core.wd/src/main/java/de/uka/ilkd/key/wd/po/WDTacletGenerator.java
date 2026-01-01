package de.uka.ilkd.key.wd.po;

import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.TacletPOGenerator;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.wd.ClassWellDefinedness;
import de.uka.ilkd.key.wd.MethodWellDefinedness;
import de.uka.ilkd.key.wd.SpecificationRepositoryWD;
import de.uka.ilkd.key.wd.WellDefinednessCheck;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 *
 * @author Alexander Weigl
 * @version 1 (1/1/26)
 */
public class WDTacletGenerator implements TacletPOGenerator {
    /**
     * Generate well-definedness taclets to resolve formulas as WD(pv.{@literal <inv>}) or
     * WD(pv.m(...)).
     *
     * @param proofConfig the proof configuration
     */
    @Override
    public void generate(AbstractPO abstractPO, InitConfig proofConfig, SpecificationRepository specRepos) {
        if (!WellDefinednessCheck.isOn()) {
            return;
        }
        ImmutableSet<RewriteTaclet> res = DefaultImmutableSet.nil();
        ImmutableSet<String> names = DefaultImmutableSet.nil();

        var repo = (SpecificationRepositoryWD)specRepos;
        for (WellDefinednessCheck ch : repo.getAllWdChecks()) {
            if (ch instanceof MethodWellDefinedness mwd) {
                // WD(callee.m(...))
                RewriteTaclet mwdTaclet = mwd.createOperationTaclet(proofConfig.getServices());
                String tName = mwdTaclet.name().toString();
                final String prefix;
                if (tName.startsWith(WellDefinednessCheck.OP_TACLET)) {
                    prefix = WellDefinednessCheck.OP_TACLET;
                } else if (tName.startsWith(WellDefinednessCheck.OP_EXC_TACLET)) {
                    prefix = WellDefinednessCheck.OP_EXC_TACLET;
                } else {
                    prefix = "";
                }
                tName = tName.replace(prefix, "");
                if (names.contains(tName)) {
                    for (RewriteTaclet t : res) {
                        if (t.find().toString().equals(mwdTaclet.find().toString())) {
                            res = res.remove(t);
                            names = names.remove(tName);
                            mwdTaclet = mwd.combineTaclets(t, mwdTaclet, proofConfig.getServices());
                        }
                    }
                }
                res = res.add(mwdTaclet);
                names = names.add(tName);
            }
        }

        // WD(a.<inv>)
        res = res.union(ClassWellDefinedness.createInvTaclet(proofConfig.getServices()));
        for (RewriteTaclet t : res) {
            abstractPO.register(t, proofConfig);
        }
    }
}
