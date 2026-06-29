package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.xcfa.model.MetaData;
import org.jetbrains.annotations.NotNull;

public class SvLibMetadata extends MetaData {

  private final String sourceName;
  private final boolean tag;

  public SvLibMetadata(String sourceName) {
    this(sourceName, false);
  }

  public SvLibMetadata(String sourceName, boolean tag) {
    this.sourceName = sourceName;
    this.tag = tag;
  }

  @Override
  @NotNull
  public MetaData combine(@NotNull MetaData other) {
    return tag || !other.isSubstantial() ? this : other;
  }

  @Override
  public boolean isSubstantial() {
    return tag;
  }

  public String getSourceName() {
    return sourceName;
  }

  public boolean isTag() {
    return tag;
  }
}
