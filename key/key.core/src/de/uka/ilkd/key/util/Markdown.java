package de.uka.ilkd.key.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class Markdown {
  private List<MarkdownElement> elements = new ArrayList<>();

  public Markdown(MarkdownElement... elements) {
    this.elements.addAll(Arrays.asList(elements));
  }

  public String toHtml() {
    StringBuilder sb = new StringBuilder();
    sb.append("<div>");
    elements.forEach(element -> sb.append(element.toHtml()));
    sb.append("</div>");

    return sb.toString();
  }

  public String toMarkdown() {
    StringBuilder sb = new StringBuilder();
    elements.forEach(element -> sb.append(element.toMarkdown()));

    return sb.toString();
  }
}

