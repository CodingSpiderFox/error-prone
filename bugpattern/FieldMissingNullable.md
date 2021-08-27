---
title: FieldMissingNullable
summary: Field is assigned (or compared against) a definitely null value but is not
  annotated @Nullable
layout: bugpattern
tags: ''
severity: SUGGESTION
---

<!--
*** AUTO-GENERATED, DO NOT MODIFY ***
To make changes, edit the @BugPattern annotation or the explanation in docs/bugpattern.
-->


## The problem
Fields that may be `null` should be annotated with `@Nullable`. For example, do
this:

```java
public class Foo {
  @Nullable private String message = "hello";
  public void reset() {
    message = null;
  }
}
```

Not this:

```java
public class Foo {
  private String message = "hello";
  public void reset() {
    message = null;
  }
}
```

## Suppression
Suppress false positives by adding the suppression annotation `@SuppressWarnings("FieldMissingNullable")` to the enclosing element.
