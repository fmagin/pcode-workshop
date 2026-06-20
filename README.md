# Extending Ghidra using P-Code Workshop

This repository contains the materials for the workshop I initially built for REcon 2026. It is based on a custom programming language called `MiniObj` that extends C with legitimate language features that make reverse engineering hard. This includes:
- a custom string format for inline strings inspired by Swift
- virtual dispatches on all methods inspired by Objective-C, C++ and Go
- reference counting methods inspired by Objective-C
- run time type information inspired by C++, Go, Swift and Objective-C


Participants are faced with a small fictious application that should be a harmless system monitor, but contains malicious logic. This logic remains invisible in the compiled binary because the application logic is hidden behind all the language features. The goal is to iteratively develop scripts to assist the decompiler until the application logic is plainly readable in the decompiler and the malicious code becomes obvious.



## Setup

If you want to avoid spoilers, grab the [latest release](https://github.com/fmagin/pcode-workshop/releases/latest) containing the participant facing materials.
Ideally that archive should be self-explainatory, in practice I need to clean up the instructions more to achieve this.


## Building

The `scripts` folder in the repo contains the full _solution_ scripts, the build process (not yet cleaned up and published) strips the part of the scripts out that serve as exercises to implement.

The rest of the files are not yet published, but I plan to clean them up and make them available for people who are interested in how the `MiniObj` language works in the background.