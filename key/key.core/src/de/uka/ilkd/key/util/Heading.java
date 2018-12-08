package de.uka.ilkd.key.util;

@Deprecated
public class Heading extends MarkdownElement {
  private String text;
  private int level;

  public Heading(String text, int level) {
      this.text = text;
      this.level = level;
  }

  public String toHtml() {
    return "<h"+level+">"+this.text+"</h"+level+">";
  }

  public String toMarkdown() {
    return new String(new char[level]).replace("\0", "#") + text;
  }

}
