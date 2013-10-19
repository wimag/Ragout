#!/usr/bin/env python

import sys
import os
import argparse
from Bio import SeqIO
from Bio.Seq import Seq
from Bio.SeqRecord import SeqRecord


import scripts.graph_partiton as gp
import scripts.breakpoint_graph as bg
import scripts.sibelia_parser as sp
import scripts.overlap as ovlp
import scripts.debrujin_refine as debrujin
from scripts.datatypes import Contig, Scaffold
from scripts.scaffold_writer import output_scaffolds
from scripts.phylogeny import Phylogeny


def calc_distance(offset, block_distance):
    if block_distance:
        return max(0, block_distance - offset)
    else:
        return 0


def extend_scaffolds(connections, sibelia_output):
    contigs = sibelia_output.get_filtered_contigs()
    contig_index = sp.build_contig_index(contigs) #sibelia_output.build_contig_index()

    scaffolds = []
    visited = set()
    counter = [0]

    def extend_scaffold(contig):
        visited.add(contig)
        scf_name = "scaffold{0}".format(counter[0])
        counter[0] += 1
        scf = Scaffold.with_contigs(scf_name, contig.blocks[0], contig.blocks[-1], [contig])
        scaffolds.append(scf)

        #go right
        while scf.right in connections:
            adjacent = connections[scf.right].end
            block_distance = connections[scf.right].distance

            assert len(contig_index[abs(adjacent)]) == 1

            contig = contigs[contig_index[abs(adjacent)][0]]
            if contig in visited:
                break

            if contig.blocks[0] == adjacent:
                offset = sibelia_output.block_offset(abs(adjacent), contig.name)
                reverse = scf.contigs[-1].sign > 0
                offset += sibelia_output.block_offset(abs(scf.right), scf.contigs[-1].name, reverse)
                distance = calc_distance(offset, block_distance)

                scf.contigs[-1].gap = distance
                scf.contigs.append(contig)
                scf.right = contig.blocks[-1]
                visited.add(contig)
                continue

            if -contig.blocks[-1] == adjacent:
                offset = sibelia_output.block_offset(abs(adjacent), contig.name, True)
                reverse = scf.contigs[-1].sign > 0
                offset += sibelia_output.block_offset(abs(scf.right), scf.contigs[-1].name, reverse)
                distance = calc_distance(offset, block_distance)

                scf.contigs[-1].gap = distance
                scf.contigs.append(contig)
                scf.contigs[-1].sign = -1
                scf.right = -contig.blocks[0]
                visited.add(contig)
                continue

            break

        #go left
        while -scf.left in connections:
            adjacent = -connections[-scf.left].end
            block_distance = connections[-scf.left].distance

            assert len(contig_index[abs(adjacent)]) == 1

            contig = contigs[contig_index[abs(adjacent)][0]]
            if contig in visited:
                break

            if contig.blocks[-1] == adjacent:
                offset = sibelia_output.block_offset(abs(adjacent), contig.name, True)
                reverse = scf.contigs[0].sign < 0
                offset += sibelia_output.block_offset(abs(scf.left), scf.contigs[0].name, reverse)
                distance = calc_distance(offset, block_distance)

                scf.contigs.insert(0, contig)
                scf.contigs[0].gap = distance
                scf.left = contig.blocks[0]
                visited.add(contig)
                continue

            if -contig.blocks[0] == adjacent:
                offset = sibelia_output.block_offset(abs(adjacent), contig.name)
                reverse = scf.contigs[0].sign < 0
                offset += sibelia_output.block_offset(abs(scf.left), scf.contigs[0].name, reverse)
                distance = calc_distance(offset, block_distance)

                scf.contigs.insert(0, contig)
                scf.contigs[0].gap = distance
                scf.contigs[0].sign = -1
                scf.left = -contig.blocks[-1]
                visited.add(contig)
                continue

            break

    for contig in contigs:
        if contig not in visited:
            extend_scaffold(contig)
    return scaffolds


def get_scaffolds(connections, sibelia_output):
    scaffolds = extend_scaffolds(connections, sibelia_output)
    scaffolds = filter(lambda s: len(s.contigs) > 1, scaffolds)
    print "Done, {0} scaffolds".format(len(scaffolds))
    return scaffolds


def parse_contigs(contigs_file):
    contigs = SeqIO.parse(contigs_file, "fasta")
    seqs = [seq for seq in contigs]
    names = [contig.id for contig in seqs]
    return seqs, names


def parse_config(filename):
    references = {}
    tree = None
    prefix = os.path.dirname(filename)

    for line in open(filename, "r"):
        line = line.strip()
        if not line:
            continue

        vals = line.split("=")
        if vals[0] == "tree":
            tree = vals[1].strip("\"")
        else:
            ref_id, filename = vals[0], vals[1].strip("\"")
            references[ref_id] = os.path.join(prefix, filename)

    return references, tree



def do_job(config_file, target_file, out_dir, block_size, skip_sibelia):
    if not os.path.isdir(out_dir):
        sys.stderr.write("Output directory doesn`t exists\n")
        return

    KMER = 55

    out_scaffolds = os.path.join(out_dir, "scaffolds.fasta")
    out_order = os.path.join(out_dir, "order.txt")
    out_ref_scaffolds = os.path.join(out_dir, "scaffolds_refined.fasta")
    out_ref_order = os.path.join(out_dir, "order_refined.txt")
    out_graph = os.path.join(out_dir, "breakpoint_graph.dot")
    out_overlap = os.path.join(out_dir, "contigs_overlap.dot")

    debug_dir = os.path.join(out_dir, "debug")
    if not os.path.isdir(debug_dir):
        os.mkdir(debug_dir)

    references, tree_string = parse_config(config_file)

    contigs_seqs, contig_names = parse_contigs(target_file)
    sibelia_output = sp.SibeliaRunner(references, target_file, block_size,
                                        out_dir, contig_names, skip_sibelia)

    graph = bg.BreakpointGraph()
    graph.build_from(sibelia_output)

    phylogeny = Phylogeny(tree_string)

    adj_finder = gp.AdjacencyFinder(graph, phylogeny, debug_dir)
    connections = adj_finder.find_adjacencies()
    scaffolds = get_scaffolds(connections, sibelia_output)

    contigs_dict = {seq.id : seq.seq for seq in contigs_seqs}
    output_scaffolds(contigs_dict, scaffolds, out_scaffolds, out_order, KMER, False)
    #graph.write_dot(open(out_graph, "w"))

    ovlp.build_graph(contigs_dict, KMER, open(out_overlap, "w"))
    refined_scaffolds = debrujin.refine_contigs(out_overlap, scaffolds)
    output_scaffolds(contigs_dict, refined_scaffolds, out_ref_scaffolds,
                                                out_ref_order, KMER, False)


def main():
    parser = argparse.ArgumentParser(description="Tool for reference-assisted assembly")
    parser.add_argument("-c", action="store", metavar="config", dest="config",
                        required=True, help="Configuration file")
    parser.add_argument("-t", action="store", metavar="target_assembly", dest="target_assembly",
                        required=True, help="File with assembly in fasta format")
    parser.add_argument("-o", action="store", metavar="output_dir", dest="output_dir",
                        required=True, help="Output directory")
    parser.add_argument("-s", action="store_const", metavar="skip_sibelia", dest="skip_sibelia",
                        default=False, const=True, help="Skip Sibelia running step")
    parser.add_argument("-m", action="store", metavar="block_size", dest="block_size",
                        default="5000", help="Sibeia minimum block size (default: 5000)")
    #parser.add_argument("-g", action="store_const", metavar="debrujin_refine", dest="debrujin_refine",
    #                    default=False, const=True, help="Refine with Debrujin graph")

    args = parser.parse_args()
    do_job(args.config, args.target_assembly, args.output_dir, args.block_size, args.skip_sibelia)

if __name__ == "__main__":
    main()