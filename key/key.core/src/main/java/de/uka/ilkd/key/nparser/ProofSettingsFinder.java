package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.settings.ProofSettings;

/**
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
public class ProofSettingsFinder extends AbstractBuilder<Void> {
    private String settings = "";

    public ProofSettings getProofSettings() {
        ProofSettings settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        settings.loadSettingsFromString(this.settings);
        return settings;
    }


    @Override
    public Void visitDecls(KeYParser.DeclsContext ctx) {
        mapOf(ctx.preferences());
        return null;
    }

    @Override
    public Void visitPreferences(KeYParser.PreferencesContext ctx) {
        var text = ctx.s.getText();
        text = text.substring(1, text.length() - 1); // remove quotes
        settings = "\n" + text;
        return null;
    }
}
