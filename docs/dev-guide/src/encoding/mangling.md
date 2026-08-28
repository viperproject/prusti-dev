# Name mangling

Viper identifiers derived from Rust items are built from the item's full definition path,
so that items with the same name in different modules do not collide. The path is then
sanitized, since Viper identifiers may not contain most of the punctuation a Rust path
does.

For example, the predicate encoding [std::ops::Range](https://doc.rust-lang.org/std/ops/struct.Range.html) is named:

```viper
predicate p_std$col$$col$ops$col$$col$Range(self) {
  ...
}
```

which is the sanitized form of `p_std::ops::Range`.

The [`SHORT_VIPER_NAMES`](../config/flags.md#short_viper_names) flag replaces the
definition path with the item's short name (here, `p_Range`), which is more readable
when inspecting generated Viper by hand. Sanitization still applies. Short names are not
unique, so enabling the flag may result in errors due to name collisions.

## Sanitization rules

The following replacements are performed (see `sanitize_char` in `vir/src/viper_ident.rs`):

| Original character | Replacement |
| --- | --- |
| `<` | `$lt$` |
| `>` | `$gt$` |
| ` ` | `$sp$` |
| `,` | `$com$` |
| `:` | `$col$` |
| `'` | `$sq$` |
| `&` | `$amp$` |
| `-` | `$hyp$` |
| `(` | `$lp$` |
| `)` | `$rp$` |
| `[` | `$lb$` |
| `]` | `$rb$` |
| `{` | `$lc$` |
| `}` | `$rc$` |
| `?` | `$qm$` |
| `;` | `$sc$` |
| `#` | `$oc$` |
| `/` | `$fs$` |
| `*` | `$as$` |
| `=` | `$eq$` |
| `+` | `$pl$` |
| `!` | `$ex$` |
