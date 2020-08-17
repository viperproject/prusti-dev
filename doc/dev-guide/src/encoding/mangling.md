# Name mangling

To ensure there are no duplicate names in the generated Viper code, name mangling is employed. Name mangling can be disabled with the [`DISABLE_NAME_MANGLING`](../config/flags.md#disable_name_mangling) flag, although this may result in errors due to name collisions.

For example, to encode the type [std::ops::Range](https://doc.rust-lang.org/std/ops/struct.Range.html), rather than generating the predicate:

```viper
predicate Range(self) {
  ...
}
```

Prusti generates:

```viper
predicate m_core$$ops$opensqu$0$closesqu$$$range$opensqu$0$closesqu$$$Range$opensqu$0$closesqu$$_beg_$i32$_end_(self) {
  ...
}
```

This is the encoded form of `m_core::ops[0]::range[0]::Range[0]$_beg_$i32$_end_`.

## Mangling rules

The following replacements are performed during name mangling:

| Original characters | Replacement |
| --- | --- |
| `::` | `$$` |
| `<` | `$openang$` |
| `>` | `$closeang$` |
| `(` | `$openrou$` |
| `)` | `$closerou$` |
| `[` | `$opensqu$` |
| `]` | `$closesqu$` |
| `{` | `$opencur$` |
| `}` | `$closecur$` |
| `,` | `$comma$` |
| `;` | `$semic$` |
| ` ` | `$space$` |
