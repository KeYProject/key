package de.uka.ilkd.key.proof.runallproofs;

import java.util.List;
import java.util.Map;
import org.antlr.runtime.Token;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit implements ProofCollectionUnit {

    final String groupName;
    List<FileWithTestProperty> files;
    Map<Token, Token> settingsMap;

    public GroupedProofCollectionUnit(Token nameToken, Map<Token, Token> settingsMap, List<FileWithTestProperty> files) {
        groupName = nameToken.getText();
        this.settingsMap = settingsMap;
        this.files = files;
    }

}
