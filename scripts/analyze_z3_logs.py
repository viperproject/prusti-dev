#!/usr/bin/env python3

"""
The Z3 log format is documented here:
https://github.com/viperproject/axiom-profiler/blob/master/LogDocumentation.pdf
"""

import sys
import re
import csv

DETAILED_ANALYSIS = True

class Parser:

    def __init__(self, line):
        self.line = line
        self.cursor = 0

    def __str__(self):
        return f'"{self.line[self.cursor:]}"'

    def remaining(self):
        return self.line[self.cursor:]

    def eof(self):
        return not self.not_eof()

    def not_eof(self):
        return self.cursor < len(self.line)

    def peek(self):
        if self.not_eof():
            return self.line[self.cursor]
        else:
            return None

    def is_number(self):
        return (self.cursor < len(self.line) and
                self.line[self.cursor].isdigit())

    def is_ident(self):
        return (self.cursor < len(self.line) and
                (self.line[self.cursor].isidentifier() or
                self.line[self.cursor].isdigit() or
                self.line[self.cursor] in '$.<>=!%@-[]'
                ))

    def is_alpha_numeric(self):
        return (self.cursor < len(self.line) and
                self.line[self.cursor].isalnum())

    def skip_whitespace(self):
        while self.not_eof() and self.peek().isspace():
            self.cursor += 1

    def consume(self, string):
        old_cursor = self.cursor
        self.skip_whitespace()
        i = 0
        while self.not_eof() and i < len(string) and self.peek() == string[i]:
            self.cursor += 1
            i += 1
        if i == len(string):
            return True
        else:
            self.cursor = old_cursor
            return False

    def parse_number(self):
        old_cursor = self.cursor
        self.skip_whitespace()
        number = 0
        while self.is_number():
            number *= 10
            number += int(self.line[self.cursor])
            self.cursor += 1
        assert old_cursor < self.cursor, f'"{self.line}" "{self.line[old_cursor:]}" {self.cursor} {old_cursor}'
        return number

    def parse_hex_number(self):
        self.skip_whitespace()
        old_cursor = self.cursor
        number = []
        while self.is_alpha_numeric():
            number.append(self.line[self.cursor])
            self.cursor += 1
        assert old_cursor < self.cursor, f'{self.line} {self.cursor} {old_cursor}'
        return int(''.join(number), 16)

    def try_parse_ident(self):
        old_cursor = self.cursor
        self.skip_whitespace()
        ident = []
        while self.is_ident():
            ident.append(self.line[self.cursor])
            self.cursor += 1
        if ident:
            return ''.join(ident)
        else:
            self.cursor = old_cursor
            return None

    def parse_ident(self):
        ident = self.try_parse_ident()
        assert ident, f'{self.line[self.cursor:]}'
        return ident

    def try_parse_id(self):
        self.skip_whitespace()
        if self.eof():
            return None
        if self.consume('datatype#'):
            return 'datatype#' + str(self.parse_number())
        elif self.consume('#'):
            return '#' + str(self.parse_number())
        else:
            return None

    def parse_id(self):
        id = self.try_parse_id()
        assert id is not None, (self.line, self.cursor)
        return id

    def parse_id_sequence(self):
        ids = []
        while True:
            id = self.try_parse_id()
            if id is None:
                break
            ids.append(id)
        return ids

    def parse_quant_term_sequence(self):
        terms = []
        while True:
            if self.consume('('):
                original = self.parse_id()
                matched = self.parse_id()
                if original == matched:
                    # optimization
                    terms.append(original)
                else:
                    terms.append((original, matched))
                assert self.consume(')')
            else:
                id = self.try_parse_id()
                if id is None:
                    break
                terms.append(id)
        return terms

    def parse_variable_decls(self):
        decls = []
        try:
            while True:
                if self.consume('('):
                    if self.consume('|'):
                        name = self.parse_ident()
                        self.consume('|')
                        self.consume(';')
                        self.consume('|')
                        ty = self.parse_ident()
                        self.consume('|')
                        self.consume(')')
                        decls.append((name, ty))
                    else:
                        self.consume(';')
                        ty = self.parse_ident()
                        self.consume(')')
                        decls.append((None, ty))
                else:
                    break
        except:
            print(self.line)
            raise
        return decls


class BaseTerm:

    def subterms(self):
        return []


class FunctionApplication(BaseTerm):
    def __init__(self, ident, args):
        self.ident = ident
        self.args = args

    def __str__(self):
        return f'{self.ident} ({len(self.args)})'

    def subterms(self):
        return self.args


class UnparsedMkApp(BaseTerm):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return f'"{self.value}"'


class Variable(BaseTerm):
    def __init__(self, index):
        self.index = index

    def __str__(self):
        return f'Var({self.index})'


class Arith(BaseTerm):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return f'arith({self.value})'


class Quantifier:
    def __init__(self, name, num_decls, patterns, body):
        self.name = name
        self.variable_decls = None
        self.num_decls = num_decls  # Number of Children in axiom-profiler
        self.patterns = patterns
        self.body = body

    def __str__(self):
        return f'{self.name}'


class Frame:

    def __init__(self):
        # Quantifier → set of term ids
        self.matched_trigger_terms = {}
        self.labels = []

    def __str__(self):
        return str(self.matched_trigger_terms)

    def __repr__(self):
        return f'{self.labels}: {self.matched_trigger_terms}'

class State:

    def __init__(self):
        self.stack = [Frame()]
        self.max_matched_trigger_terms = {}
        # Quantifiers that are triggered multiple times with the same
        # trigger.
        self.multi_match_quantifier = {}

    def register_matched_trigger_term(self, quantifier_id, term_id):
        for frame in self.stack:
            if quantifier_id in frame.matched_trigger_terms:
                if term_id in frame.matched_trigger_terms[quantifier_id]:
                    if quantifier_id not in self.multi_match_quantifier:
                        self.multi_match_quantifier[quantifier_id] = 0
                    self.multi_match_quantifier[quantifier_id] += 1
        if quantifier_id not in self.stack[-1].matched_trigger_terms:
            self.stack[-1].matched_trigger_terms[quantifier_id] = set()
        self.stack[-1].matched_trigger_terms[quantifier_id].add(term_id)
        count = 0
        for frame in self.stack:
            try:
                count += len(frame.matched_trigger_terms[quantifier_id])
            except KeyError:
                pass
        if (quantifier_id not in self.max_matched_trigger_terms or
                self.max_matched_trigger_terms[quantifier_id] < count):
            self.max_matched_trigger_terms[quantifier_id] = count

    def append_label(self, label):
        self.stack[-1].labels.append(label)

    def push(self):
        self.stack.append(Frame())

    def pop(self):
        self.stack.pop()


class MessageAnalyzer:

    def __init__(self, csv_writer):
        self.csv_writer = csv_writer
        self.quantifiers = {}
        self.quantifier_matches = {}
        self.quantifier_match_count = {}
        self.quantifier_instantiation_count = {}
        self.triggers = {}
        self.term_definitions = {}
        self.state = State()
        self.unique_terms = set()

    def analyze(self, kind, value, message):
        kind_ident = kind.replace('-', '_')
        method_name = f'analyze_{kind_ident}'
        kind_analyzer = getattr(self, method_name)
        kind_analyzer(value, message)

    def analyze_assign(self, value, message):
        # assert len(message) == 1, message
        pass

    def analyze_attach_enode(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_attach_meaning(self, value, message):
        assert len(message) == 1, message
        parser = Parser(value)
        term_id = parser.parse_id()
        if parser.consume('arith'):
            value = parser.remaining().strip()
            self.term_definitions[term_id] = Arith(value)

    def analyze_attach_var_names(self, value, message):
        assert len(message) == 1, message
        parser = Parser(value)
        quantifier_id = parser.parse_id()
        variable_decls = parser.parse_variable_decls()
        parser.skip_whitespace()
        assert parser.eof(), parser

        self.quantifiers[quantifier_id].variable_decls = variable_decls

    def analyze_begin_check(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_conflict(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_decide_and_or(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_end_of_instance(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_eq_expl(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_inst_discovered(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_instance(self, value, message):
        assert len(message) == 1, message
        if DETAILED_ANALYSIS:
            parser = Parser(value)
            fingerprint = parser.parse_hex_number()
            result_term_id = parser.parse_id()
            parser.skip_whitespace()
            # assert parser.eof(), parser

            if fingerprint != 0:
                quantifier_id = self.quantifier_matches[fingerprint]
                self.quantifier_instantiation_count[quantifier_id] += 1

    def analyze_mk_app(self, value, message):
        assert len(message) == 1, message
        if DETAILED_ANALYSIS:
            parser = Parser(value)
            term_id = parser.parse_id()
            # try:
                # self.state.register(term_id, parser.remaining())
            # except:
                # print(message)
                # raise
            if parser.consume('pattern'):
                expr_ids = parser.parse_id_sequence()
                parser.skip_whitespace()
                assert parser.eof(), parser
                self.triggers[term_id] = expr_ids
                return
            ident = parser.try_parse_ident()
            if ident is not None:
                if ident.startswith('basic_block_marker'):
                    self.state.append_label(ident)
                else:
                    args = parser.parse_id_sequence()
                    parser.skip_whitespace()
                    assert parser.eof(), parser
                    self.term_definitions[term_id] = FunctionApplication(ident, args)
            else:
                self.term_definitions[term_id] = UnparsedMkApp(value)

    def analyze_mk_lambda(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_mk_proof(self, value, message):
        assert len(message) == 1, message
        pass

    def analyze_mk_quant(self, value, message):
        assert len(message) == 1, message
        parser = Parser(value)
        quantifier_id = parser.parse_id()
        quantifier_name = parser.parse_ident()
        num_decls = parser.parse_number()
        (*patterns, body) = parser.parse_id_sequence()
        parser.skip_whitespace()
        assert parser.eof(), parser

        self.quantifier_match_count[quantifier_id] = 0
        self.quantifier_instantiation_count[quantifier_id] = 0
        self.quantifiers[quantifier_id] = Quantifier(
            quantifier_name, num_decls, patterns, body
        )

    def analyze_mk_var(self, value, message):
        assert len(message) == 1, message
        parser = Parser(value)
        term_id = parser.parse_id()
        index = parser.parse_number()
        parser.skip_whitespace()
        assert parser.eof(), parser
        self.term_definitions[term_id] = Variable(index)

    def analyze_new_match(self, value, message):
        """
        https://github.com/Z3Prover/z3/wiki/Equality-Explanation-Logging#new-matches
        """
        assert len(message) == 1, message
        parser = Parser(value)
        fingerprint = parser.parse_hex_number()
        quantifier_id = parser.parse_id()
        trigger_id = parser.parse_id()
        variable_instantiations = parser.parse_id_sequence()
        assert parser.consume(';')
        matched_terms = parser.parse_quant_term_sequence()
        parser.skip_whitespace()
        assert parser.eof(), parser

        self.quantifier_matches[fingerprint] = quantifier_id
        self.quantifier_match_count[quantifier_id] += 1

        if DETAILED_ANALYSIS:
            quantifier = self.quantifiers[quantifier_id]
            self.add_row([
                quantifier_id,
                quantifier.name,
            ])
            for term in matched_terms:
                try:
                    (original, matched) = term
                    self.add_row([
                        quantifier_id,
                        self.render_term(original),
                        self.render_term(matched),
                    ])
                    self.state.register_matched_trigger_term(quantifier_id, original)
                    self.state.register_matched_trigger_term(quantifier_id, matched)
                    assert quantifier_id != '#3634'
                except ValueError:
                    # if quantifier_id == '#3634':
                        # self.unique_terms.add(term)
                        # self.unique_terms.add(self.render_term(term))
                        # try:
                            # self.state.register(term, None)
                        # except:
                            # print(message)
                            # raise
                        # self.state.register_matched_trigger_term(quantifier_id, term)

                    self.state.register_matched_trigger_term(quantifier_id, term)
                    self.add_row([
                        quantifier_id,
                        self.render_term(term),
                    ])

            # if self.quantifier_match_count[quantifier_id] > 300:
                # if quantifier_id == '#3634':
                    # print(value)
                    # print()

                    # self.show_quantifier(quantifier_id)

                    # print()
                    # print()

                    # print('matched-trigger:')
                    # self.show_trigger(trigger_id, variables=variable_instantiations)

                    # self.show_term('#3808')
                    # self.show_term('#971')

                    # print('matched terms:')
                    # for term in matched_terms:
                        # try:
                            # (original, matched) = term
                            # print('original:')
                            # self.show_term(original)
                            # print('replacing matched:')
                            # self.show_term(matched)
                        # except:
                            # print('matched:')
                            # self.show_term(term)

    def analyze_pop(self, value, message):
        assert len(message) == 1
        if DETAILED_ANALYSIS:
            parser = Parser(value)
            scopes_to_pop = parser.parse_number()
            scopes_active = parser.parse_number()
            parser.skip_whitespace()
            assert parser.eof(), parser

            assert scopes_active == len(self.state.stack) - 1
            while scopes_to_pop > 0:
                self.state.pop()
                scopes_to_pop -= 1

    def analyze_push(self, value, message):
        assert len(message) == 1
        if DETAILED_ANALYSIS:
            parser = Parser(value)
            scopes_active = parser.parse_number()
            parser.skip_whitespace()
            assert parser.eof(), parser

            assert scopes_active == len(self.state.stack) - 1
            self.state.push()

    def analyze_resolve_lit(self, value, message):
        assert len(message) == 1
        pass

    def analyze_resolve_process(self, value, message):
        assert len(message) == 1
        pass

    def analyze_tool_version(self, value, message):
        assert len(message) == 1
        pass

    def process_message(self, message):
        if not message:
            return
        (kind, value) = parse_message_header(message[0])
        self.analyze(kind, value, message)

    def render_term(self, term_id, depth=10):
        if depth == 0:
            return '…'
        try:
            term = self.term_definitions[term_id]
        except KeyError:
            return 'n/a'
        else:
            parts = ['( ', str(term)]
            for arg in term.subterms():
                parts.append(self.render_term(arg, depth-1))
            parts.append(')')
            return ' '.join(parts)

    def show_term(self, term_id, depth=5, step=0, variables=None):
        separator = '  ' * step
        if depth == 0:
            print(f'{separator}{term_id}: bound-reached')
            return
        try:
            term = self.term_definitions[term_id]
        except KeyError:
            print(f'{separator}{term_id}: not-found')
        else:
            if type(term) == Variable and variables is not None:
                print(f'{separator}{term_id}: {variables[term.index]}')
            else:
                print(f'{separator}{term_id}: {term}')
                for arg in term.subterms():
                    self.show_term(arg, depth-1, step+1, variables)

    def show_quantifier(self, quantifier_id):
        quantifier = self.quantifiers[quantifier_id]
        variables = [
            f'{name}: {ty}' for (name, ty) in quantifier.variable_decls
        ]
        print(f'forall {quantifier_id} {quantifier.name} {", ".join(variables)}')
        self.show_term(quantifier.body, step=1, variables=variables)
        print('  triggers:')
        for trigger_id in quantifier.patterns:
            self.show_trigger(trigger_id, step=1, variables=variables)
            # trigger_expr_id = self.triggers[pattern_id]
            # self.show_term(trigger_expr_id, step=1, variables=variables)

    def show_trigger(self, trigger_id, step=0, variables=None):
        for trigger_expr_id in self.triggers[trigger_id]:
            self.show_term(trigger_expr_id, step=step, variables=variables)

    def add_row(self, row):
        if self.csv_writer is not None:
            self.csv_writer.writerow(row)


def parse_message_header(line: str):
    parser = Parser(line)
    if parser.consume('['):
        kind = parser.parse_ident()
        assert kind[-1] == ']'
        return (kind[:-1], parser.remaining())
    else:
        return None

def starts_new_message(line: str) -> bool:
    return parse_message_header(line) is not None


def main(log_file_path, csv_file_path):
    with open(log_file_path, 'r') as fp:
        with open(csv_file_path, 'w') as fout:
            writer = csv.writer(fout)
            analyzer = MessageAnalyzer(csv_writer=writer)
            message = []
            for line_number, line in enumerate(fp):
                if line_number % 100000 == 0:
                    print(f'Analyzed {line_number} lines')
                # if line_number > 100000:
                #     break
                if starts_new_message(line):
                    analyzer.process_message(message)
                    message = [line]
                else:
                    message.append(line)

    print('Quantifiers matched more than 100 times (without taking '
          'push/pop into account):')
    quantifier_matches = [
        (count, id) for (id, count) in analyzer.quantifier_match_count.items()
    ]
    quantifier_matches.sort()
    for (count, id) in quantifier_matches:
        if count >= 100:
            print(id, analyzer.quantifiers[id], count)

    print()
    print('Quantifiers matched more than 10 times (with taking '
          'push/pop into account; if severely different from the '
          'previous one, consider preinstantiating quantifiers):')
    quantifier_unique_matches = [
        (count, id) for (id, count) in analyzer.state.max_matched_trigger_terms.items()
    ]
    quantifier_unique_matches.sort()
    for (count, id) in quantifier_unique_matches:
        if count >= 10:
            print(id, analyzer.quantifiers[id], count)

    print()
    print('Quantifiers that were triggered multiple times with the same trigger:')
    print(analyzer.state.multi_match_quantifier)


    print()
    print('Quantifiers instantiated more than 100 times (without taking '
          'push/pop into account; should be identical to the first list):')
    quantifier_instantiations = [
        (count, id) for (id, count) in analyzer.quantifier_instantiation_count.items()
    ]
    quantifier_instantiations.sort()
    for (count, id) in quantifier_instantiations:
        if count >= 100:
            print(id, analyzer.quantifiers[id], count)

    print()
    print()

    analyzer.show_quantifier('#2884')
    import pdb; pdb.set_trace()

    assert len(analyzer.state.stack) == 1, analyzer.state.stack

    # This function can be used show more information about a specific
    # quantifier.
    # analyzer.show_quantifier('#3634')



    # id = '#1058'
    # print(analyzer.quantifiers[id])
    # print(analyzer.quantifiers[id].variable_decls)
    # print(analyzer.quantifiers[id].expr)
    # analyzer.show_term(analyzer.quantifiers[id].expr)

    # for pattern in analyzer.quantifiers[id].patterns:
        # print(pattern)
        # trigger_expr_id = analyzer.triggers[pattern]
        # print(trigger_expr_id)
        # analyzer.show_term(trigger_expr_id)

    # print('\n\nunique triggering terms for #3634:')
    # for term in sorted(analyzer.unique_terms):
        # print(term)


if __name__ == '__main__':
    main(*sys.argv[1:])
