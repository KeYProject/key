package de.uka.ilkd.key.util;

public class PreFormatted extends MarkdownElement {
  private String text;

  public PreFormatted(String text) {
    this.text = text;
  }

  public String toHtml() {
    return "<pre>" + text.replaceAll("<", "&sm;").replaceAll(">", "&gt;") + "</pre>";
  }

  public String toMarkdown() {
    return "```\n"+text+"\n```\n";
  }
}
