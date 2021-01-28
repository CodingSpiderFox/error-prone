---
title: BanSerializableRead
summary: Deserializing user input via the `Serializable` API is extremely dangerous
layout: bugpattern
tags: ''
severity: ERROR
---

<!--
*** AUTO-GENERATED, DO NOT MODIFY ***
To make changes, edit the @BugPattern annotation or the explanation in docs/bugpattern.
-->


## The problem
The Java `Serializable` API is very powerful, and very dangerous. Any
consumption of a serialized object that cannot be explicitly trusted will likely
result in a critical remote code execution bug that will give an attacker
control of the application. (See
[Effective Java 3rd Edition §85][ej3e-85])

[ej3e-85]: https://www.google.co.uk/books/edition/Effective_Java/ka2VUBqHiWkC

Consider using less powerful serialization methods, such as JSON or XML.

## Suppression
Suppress false positives by adding the suppression annotation `@SuppressWarnings("BanSerializableRead")` to the enclosing element.
