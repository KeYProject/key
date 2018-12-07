package de.uka.ilkd.key.util.script;

/**
 * @author Alexander Weigl
 * @version 1 (07.12.18)
 */
public class UserNoteInteraction extends Interaction {
    private String note;

    public UserNoteInteraction() {
    }

    public UserNoteInteraction(String note) {
        this.note = note;
    }


    public String getNote() {
        return note;
    }

    public void setNote(String note) {
        this.note = note;
    }

    @Override
    public String toString() {
        return note;
    }

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        sb
            .append("------\n")
            .append("## UserNoteInteraction ")
            .append("\n")
            .append("### Content:\n")
            .append("```\n")
            .append(note)
            .append("\n```")
            .append("\n\n");

        return sb.toString();
    }
}
