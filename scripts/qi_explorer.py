#!/usr/bin/env python3.8

import sys
import argparse
import csv

class Explorer:
    def __init__(self, max_num_instantiations):
        self.max_num_instantiations = max_num_instantiations
        self.quantifiers = {}
        self.used_quantifiers = {}
        self.quant_to_qid = {}
        self.matches = {}
        self.instantiations = []
        self.events = []
        self.max_generation = 0

    def parse(self, path=None):
        if path:
            print(f"Loading trace file '{path}'...")
        else:
            print(f"Loading trace from stdin...")
        with open(path, "r") if path else sys.stdin as inf:
            for line in inf:
                self.parse_line(line.strip())
                if self.max_num_instantiations and len(self.instantiations) >= self.max_num_instantiations:
                    print(f"Only the first {self.max_num_instantiations} quantifier instantiations will be loaded.")
                    break

    def parse_line(self, line):
        if not line:
            return
        
        #print(f"{line=}")
        if " " in line:
            kind, line_content = line.split(" ", 1)
        else:
            kind = line
            line_content = ""

        if kind == "[tool-version]":
            print(f"Tool version: {line_content}")
        
        elif kind == "[mk-quant]":
            quant, qid, *_ = line_content.split(" ")
            self.quant_to_qid[quant] = qid
            if qid not in self.quantifiers:
                self.quantifiers[qid] = len(self.quantifiers)
            #print(f"Make quantifier {quant=}, {qid=}, {num_decls=}, {patters=}, {expr=}")
        
        elif kind == "[new-match]":
            words, comment = line_content.split(";", 1)
            fingerprint, quant, *_ = words.strip().split(" ")
            qid = self.quant_to_qid[quant]
            self.matches[fingerprint] = quant
            self.events.append(("MATCH", qid))
            #print(f"New match {fingerprint=}, {quant=}")
            if qid not in self.used_quantifiers:
                self.used_quantifiers[qid] = len(self.used_quantifiers)

        elif kind == "[instance]":
            if ";" in line_content:
                words, comment = line_content.split(";", 1)
                fingerprint, *_ = words.strip().split(" ")
                generation = int(comment.strip())
                quant = self.matches[fingerprint]
                qid = self.quant_to_qid[quant]
                #print(f"New instance {fingerprint=}, {proof_id=}, {generation=}, {quant=}, {qid=}")
                self.instantiations.append((qid, generation))
                self.events.append(("INST", qid, generation))
                self.max_generation = max(self.max_generation, generation)
                if qid not in self.used_quantifiers:
                    self.used_quantifiers[qid] = len(self.used_quantifiers)

    def get_events(self, skip_instantiations):
        if skip_instantiations:
            print(f"The first {skip_instantiations} quantifier instantiations will be ignored.")
        if not self.events:
            return
        first_event_index = 0
        while skip_instantiations > 0 and first_event_index < len(self.events):
            event = self.events[first_event_index]
            if event[0] == "INST":
                skip_instantiations -= 1
            first_event_index += 1
        return self.events[first_event_index:]

    def write_csv(self, path, skip_instantiations=0):
        print(f"Creating CSV file at '{path}'...")
        with open(path, "w", encoding="UTF8") as outf:
            writer = csv.writer(outf)
            writer.writerow(("Quantifier ID", "Generation"))
            for (qid, generation) in self.instantiations[skip_instantiations:]:
                writer.writerow((qid, generation))
        print("CSV file created")

    def write_image(self, svg_path, png_path, skip_instantiations=0):
        print("Creating SVG image...")
        import svgwrite

        events = self.get_events(skip_instantiations)
        if not events:
            print("There are no quantifier instantiations to draw.")
            return

        scale = 20
        max_height = 32700
        scale_qi_y = min(scale, max_height / len(events))
        dwg = svgwrite.Drawing(
            svg_path,
            profile="tiny",
            size=(scale * len(self.used_quantifiers), scale_qi_y * len(events))
        )

        # Write events
        for (i, event) in enumerate(events):
            if event[0] == "INST":
                qid, generation = event[1:]
                q_index = self.used_quantifiers[qid]
                opacity = 0.3 + (0.7 * generation / self.max_generation)
                dwg.add(dwg.rect(
                    insert=(scale * q_index, scale_qi_y * i),
                    size=(scale, scale_qi_y),
                    fill="red",
                    fill_opacity=opacity,
                ))
            elif event[0] == "MATCH":
                qid = event[1]
                q_index = self.used_quantifiers[qid]
                dwg.add(dwg.rect(
                    insert=(scale * q_index, scale_qi_y * i),
                    size=(scale, scale_qi_y),
                    fill="green",
                ))

        # Write quantifier names
        for delta in range(0, len(events), 500):
            for qid, q_index in self.used_quantifiers.items():
                x = scale * (0.2 + q_index)
                y = scale * 0.2 + scale_qi_y * delta
                dwg.add(dwg.text(
                    qid,
                    insert=(x, y),
                    fill="black",
                    transform=f"rotate(90,{x},{y})",
                ))

        print("SVG image created")

        if svg_path:
            print(f"Creating SVG file at '{svg_path}'...")
            dwg.save()
            print("SVG file created")

        if png_path:
            from cairosvg import svg2png
            print(f"Creating PNG file at '{png_path}'...")
            svg2png(bytestring=dwg.tostring(), write_to=png_path)
            print("PNG file created")

    def write_midi(self, path, bpm, skip_instantiations=0):
        print(f"Creating MIDI file at '{path}'...")
        from midiutil.MidiFile import MIDIFile

        # Define a MIDI file
        mf = MIDIFile(1)     # only 1 track
        track = 0   # the only track
        
        # Define a track
        time = 0    # start at the beginning
        channel = 0
        mf.addTrackName(track, time, "Quantifier instantiations")
        mf.addTempo(track, time, bpm)
        mf.addProgramChange(track, channel,  0, 0)  # Acoustic Grand Piano

        # Write instantiations
        for (i, (qid, generation)) in enumerate(self.instantiations[skip_instantiations:]):
            q_index = self.used_quantifiers[qid]
            time = i
            duration = 1         # 1 beat long
            pitch = 30 + q_index
            volume = 27 + (100 * generation // self.max_generation) 
            mf.addNote(track, channel, pitch, time, duration, volume)

        with open(path, "wb") as outf:
            mf.writeFile(outf)
        print("MIDI file created")


def parse_args():
    parser = argparse.ArgumentParser(description="Explore quantifier instantiations.")
    parser.add_argument(
        "-i", "--input",
        help="path of the Z3 trace (default: read from stdin)",
    )
    parser.add_argument(
        "--csv",
        help="output path of the CSV file",
    )
    parser.add_argument(
        "--svg",
        help="output path of the SVG file",
    )
    parser.add_argument(
        "--png",
        help="output path of the PNG file",
    )
    parser.add_argument(
        "--midi",
        help="output path of the MIDI file",
    )
    parser.add_argument(
        "--max-instantiations",
        type=int,
        help="maximum number of quantifier instantiations to load (default: all)",
    )
    parser.add_argument(
        "--skip-instantiations",
        type=int,
        default=0,
        help="number of *loaded* quantifier instantiations to skip (default: 0)",
    )
    parser.add_argument(
        "--tempo",
        type=int,
        default=480,
        help="beats per minute (default: 480)",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    explorer = Explorer(args.max_instantiations)
    explorer.parse(args.input)

    print(f"Number of quantifiers: {len(explorer.quantifiers)}")
    print(f"Number of used quantifiers: {len(explorer.used_quantifiers)}")
    print(f"Number of unique matches: {len(explorer.matches)}")
    print(f"Number of quantifier instantiations: {len(explorer.instantiations)}")

    if args.csv:
        explorer.write_csv(args.csv, args.skip_instantiations)

    if args.svg or args.png:
        explorer.write_image(args.svg, args.png, args.skip_instantiations)

    if args.midi:
        explorer.write_midi(args.midi, args.tempo, args.skip_instantiations)


if __name__ == "__main__":
    main()
