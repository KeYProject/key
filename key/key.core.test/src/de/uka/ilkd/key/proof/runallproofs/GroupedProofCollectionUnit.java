package de.uka.ilkd.key.proof.runallproofs;

import java.util.List;
import java.util.Map;
import org.antlr.runtime.Token;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit extends ProofCollectionUnit {

    final String groupName;
    List<FileWithTestProperty> files;
//    Map<String, Object> settingsMap;

    public GroupedProofCollectionUnit(Token nameToken, Map<Token, Token> settingsMap, List<FileWithTestProperty> files) {
        groupName = nameToken.getText();
//        this.settingsMap = new HashMap<>();
        this.files = files;
    }

   @Override
   public boolean processProofObligations() {
      for(FileWithTestProperty file : files){
         System.out.println(file.path);
      }
      return true;
   }

}
