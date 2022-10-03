import os
import time

from parser import SpyroSygusParser
from synth import SynthesisOracle
from soundness import SoundnessOracle
from precision import PrecisionOracle
from util import *
import cvc5


class PropertySynthesizer:
    def __init__(self, infile, outfile):

        # Input/Output file stream
        self.__infile = infile
        self.__outfile = outfile
      
        # Template for Sketch synthesis
        self.__ast = SpyroSygusParser().parse(self.__infile.read())

        # Iterators
        self.__outer_iterator = 0
        self.__inner_iterator = 0

        # Primitives
        self.__synthesis_oracle = SynthesisOracle(self.__ast)
        self.__soundness_oracle = SoundnessOracle(self.__ast)
        self.__precision_oracle = PrecisionOracle(self.__ast)

    def __write_output(self, output):
        self.__outfile.write(output)     

    def __synthesize(self, pos, neg_must, neg_may, lam_functions):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Try synthesis')   

        # Run Sketch with temp file
        start_time = time.time()
        phi = self.__synthesis_oracle.synthesize()
        end_time = time.time()
        
        # Update statistics
        elapsed_time = end_time - start_time

        # Return the result
        if phi != None:
            return phi
        else:
            return None

    def __check_soundness(self, phi):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Check soundness')

        # Run Sketch with temp file
        start_time = time.time()
        e_pos = self.__soundness_oracle.check_soundness(phi)
        end_time = time.time()

        # Statistics
        elapsed_time = end_time - start_time

        # Return the result
        if e_pos != None:
            return (e_pos, False)
        else:
            return (None, elapsed_time >= self.__timeout)

    def __check_precision(self, phi, phi_list, pos, neg_must, neg_may, lam_functions):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} - {self.__inner_iterator}: Check precision')

        # Run Sketch with temp file
        start_time = time.time()
        e_neg, phi = self.__precision_oracle.check_precision(phi)
        end_time = time.time()

        # Update statistics
        elapsed_time = end_time - start_time

        # Return the result
        if output != None:
            return (e_neg, phi)
        else:
            self.__time_last_query = elapsed_time
            return (None, None)

    def __check_improves_predicate(self, phi_list, phi, lam_functions):
        if self.__verbose:
            print(f'Iteration {self.__outer_iterator} : Check termination')

        # Run Sketch with temp file
        code = self.__input_generator.generate_improves_predicate_input(phi, phi_list, lam_functions)           
        output, _ = self.__try_synthesis(code)

        # Return the result
        if output != None:
            output_parser = OutputParser(output)
            e_neg = output_parser.parse_improves_predicate()
            return e_neg
        else:
            return None

    def __synthesizeProperty(self, phi_list, phi_init, pos, neg_must):
        # Assume that current phi is sound
        phi_e = phi_init
        phi_last_sound = None

        while True:
            e_pos, lam, timeout = self.__check_soundness(phi_e)
            if e_pos != None:
                pos.append(e_pos)
                
                # First try synthesis
                phi, lam = self.__synthesize(pos, neg_must, neg_may, lam_functions)
                
                # If neg_may is a singleton set, it doesn't need to call MaxSynth
                # Revert to the last remembered sound property 
                if phi == None and len(neg_may) == 1 and phi_last_sound != None:
                    phi = phi_last_sound
                    neg_delta += neg_may
                    neg_may = []
                    lam = {}

                # MaxSynth 
                elif phi == None:
                    neg_may, delta, phi, lam = self.__max_synthesize(
                        pos, neg_must, neg_may, lam_functions, phi_last_sound)
                    neg_delta += delta
                
                    # MaxSynth can't minimize the term size, so call the Synth again
                    if self.__input_generator.minimize_terms_enabled:
                        phi, lam = self.__synthesize(pos, neg_must, neg_may, lam_functions)

                phi_e = phi
                lam_functions = union_dict(lam_functions, lam)
            
            # Return the last sound property found
            elif timeout and phi_last_sound != None:
                neg_delta = self.__filter_neg_delta(phi_last_sound, neg_delta, lam_functions)
                return (phi_last_sound, pos, neg_must + neg_may, neg_delta, lam_functions)

            elif timeout:
                return (self.__phi_truth, pos, [], [], lam_functions)

            # Early termination after finding a sound property with negative example
            elif not most_precise and len(neg_may) > 0:
                neg_delta = self.__filter_neg_delta(phi_e, neg_delta, lam_functions)
                return (phi_e, pos, neg_must + neg_may, neg_delta, lam_functions)
            
            # Check precision after pass soundness check
            else:
                phi_last_sound = phi_e    # Remember the last sound property

                if update_psi and len(neg_may) > 0:
                    phi_list = phi_list + [phi_e]

                # If phi_e is phi_truth, which is initial candidate of the first call,
                # then phi_e doesn't rejects examples in neg_may. 
                if self.__move_neg_may:
                    neg_must += neg_may
                    neg_may = []

                e_neg, phi, lam = self.__check_precision(
                    phi_e, phi_list, pos, neg_must, neg_may, lam_functions)
                if e_neg != None:   # Not precise
                    phi_e = phi
                    neg_may.append(e_neg)
                    lam_functions = lam
                else:               # Sound and Precise
                    neg_delta = self.__filter_neg_delta(phi_e, neg_delta, lam_functions)
                    return (phi_e, pos, neg_must + neg_may, neg_delta, lam_functions)

    def __synthesizeAllProperties(self):
        phi_list = []
        pos = []
        neg_may = []
        lam_functions = {}

        while True:

            if len(neg_may) > 0:
                neg_may, _, phi_init, lam = self.__max_synthesize(
                    pos, [], neg_may, lam_functions, self.__phi_truth)
                lam_functions = union_dict(lam_functions, lam)
            else:
                phi_init = self.__phi_truth

            most_precise = self.__minimize_terms
            phi, pos, neg_must, neg_may, lam = \
                self.__synthesizeProperty(
                    phi_list, phi_init, pos, [], neg_may, lam_functions, 
                    most_precise, self.__update_psi)
            lam_functions = lam

            # Check if most precise candidates improves property. 
            # If neg_must is nonempty, those examples are witness of improvement.
            if len(neg_must) == 0:
                e_neg = self.__check_improves_predicate(phi_list, phi, lam_functions)
                if e_neg != None:
                    neg_must = [e_neg]
                else:
                    stat = self.__statisticsCurrentProperty(pos, neg_must, neg_may, [], [])
                    self.__statistics.append(stat)
                    return

            if self.__minimize_terms: 
                self.__input_generator.enable_minimize_terms()
                
                # Synthesize a new candidate, which is minimized
                # We can always synthesize a property here
                phi, lam = self.__synthesize(pos, neg_must, [], lam_functions)

            # Strengthen the found property to be most precise L-property
            phi, pos, neg_used, neg_delta, lam = \
                self.__synthesizeProperty([], phi, pos, neg_must, [], lam_functions, True, False)

            stat = self.__statisticsCurrentProperty(pos, neg_must, neg_may, neg_used, neg_delta)
            self.__statistics.append(stat)
            self.__resetStatistics()

            phi_list.append(phi)

            if self.__verbose:
                print("Obtained a best L-property")
                print(phi + '\n')

                for function_name, code in lam_functions.items():
                    if function_name in phi:
                        print(value + '\n')

            self.__outer_iterator += 1
            self.__inner_iterator = 0
    
    def run(self):
        self.__synthesizeAllProperties()