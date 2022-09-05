#!/bin/env python3
# -*- coding: utf-8 -*-
### vim:set ts=4 sw=4 sts=0 fenc=utf-8: ###

###
### $Id:$
###

"""
G-CODE viewer
"""

import sys
import re
import io
import getopt
import math
import numpy        as np
import traceback
import itertools
import collections
import functools
import threading
import os.path
import time
import base64
import xml.sax
import xml.sax.handler
import tkinter              as tk
import tkinter.ttk          as ttk
import tkinter.filedialog   as tkfd
import tkinter.messagebox   as tkmb

import skia
import tkinterdnd2 as tkdnd
from PIL import Image, ImageTk

#

SCRIPT_NAME = "G-CODE viewer"

DEFAULT_WIN_WIDTH = 1200
DEFAULT_WIN_HEIGHT = 800
DEFAULT_WIN_WIDTH_MIN = 600
DEFAULT_WIN_HEIGHT_MIN = 400

ZOOM_DEFAULT = 3
ZOOM_MIN = 1.5
ZOOM_MAX = 60
ZOOM_TICK = 0.5

DEFAULT_BED_W = 250
DEFAULT_BED_H = 210
DEFAULT_BED_M = 10

FILETYPES = ( ("g-code", "*.gcode"), ("all", "*.*") )

def usage( self ):
    pass

def parse_option( self ):
    pass

def matrix_tran(tx, ty):
    return np.array([[1, 0, tx],
                     [0, 1, ty],
                     [0, 0, 1]])

def matrix_rot(a):
    return np.array([[np.cos(a), -np.sin(a), 0],
                     [np.sin(a),  np.cos(a), 0],
                     [        0,          0, 1]])

def matrix_shear(mx, my):
    return np.array([[1, -mx, 0],
                     [-my, 1, 0],
                     [0,  0, 1]])

def matrix_scale(sx, sy):
    return np.array([[sx, 0, 0],
                     [0, sy, 0],
                     [0,  0, 1]])
ICON_ZOOM_IN = '''
<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" class="bi bi-zoom-in" viewBox="0 0 16 16">
  <path fill-rule="evenodd" d="M6.5 12a5.5 5.5 0 1 0 0-11 5.5 5.5 0 0 0 0 11zM13 6.5a6.5 6.5 0 1 1-13 0 6.5 6.5 0 0 1 13 0z"/>
  <path d="M10.344 11.742c.03.04.062.078.098.115l3.85 3.85a1 1 0 0 0 1.415-1.414l-3.85-3.85a1.007 1.007 0 0 0-.115-.1 6.538 6.538 0 0 1-1.398 1.4z"/>
  <path fill-rule="evenodd" d="M6.5 3a.5.5 0 0 1 .5.5V6h2.5a.5.5 0 0 1 0 1H7v2.5a.5.5 0 0 1-1 0V7H3.5a.5.5 0 0 1 0-1H6V3.5a.5.5 0 0 1 .5-.5z"/>
</svg>
'''

ICON_ZOOM_OUT = '''
<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" class="bi bi-zoom-out" viewBox="0 0 16 16">
  <path fill-rule="evenodd" d="M6.5 12a5.5 5.5 0 1 0 0-11 5.5 5.5 0 0 0 0 11zM13 6.5a6.5 6.5 0 1 1-13 0 6.5 6.5 0 0 1 13 0z"/>
  <path d="M10.344 11.742c.03.04.062.078.098.115l3.85 3.85a1 1 0 0 0 1.415-1.414l-3.85-3.85a1.007 1.007 0 0 0-.115-.1 6.538 6.538 0 0 1-1.398 1.4z"/>
  <path fill-rule="evenodd" d="M3 6.5a.5.5 0 0 1 .5-.5h6a.5.5 0 0 1 0 1h-6a.5.5 0 0 1-.5-.5z"/>
</svg>
'''

### non bootstrap icon ( mixed bi-zoom-in and bi-bootstrap-reboot )
ICON_ZOOM_RESET = '''
<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" class="" viewBox="0 0 16 16">
  <path fill-rule="evenodd" d="M6.5 12a5.5 5.5 0 1 0 0-11 5.5 5.5 0 0 0 0 11zM13 6.5a6.5 6.5 0 1 1-13 0 6.5 6.5 0 0 1 13 0z"/>
  <path d="M10.344 11.742c.03.04.062.078.098.115l3.85 3.85a1 1 0 0 0 1.415-1.414l-3.85-3.85a1.007 1.007 0 0 0-.115-.1 6.538 6.538 0 0 1-1.398 1.4z"/>
  <path transform="matrix( 1 0 -1.5 0 1 -1.5 )" d="M6.641 11.671V8.843h1.57l1.498 2.828h1.314L9.377 8.665c.897-.3 1.427-1.106 1.427-2.1 0-1.37-.943-2.246-2.456-2.246H5.5v7.352h1.141zm0-3.75V5.277h1.57c.881 0 1.416.499 1.416 1.32 0 .84-.504 1.324-1.386 1.324h-1.6z"/>
  </svg>
'''

ICON_UP = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M17.6569 16.2427L19.0711 14.8285L12.0001 7.75739L4.92896 14.8285L6.34317 16.2427L12.0001 10.5858L17.6569 16.2427Z" fill="currentColor" /></svg>
'''

ICON_DOWN = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M6.34317 7.75732L4.92896 9.17154L12 16.2426L19.0711 9.17157L17.6569 7.75735L12 13.4142L6.34317 7.75732Z" fill="currentColor" /></svg>
'''

ICON_FORWARD_SKIP = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M7.41421 5L6 6.41421L11.6569 12.0711L6 17.7279L7.41421 19.1421L14.4853 12.0711L7.41421 5Z" fill="currentColor" /><path d="M16.3432 19V5H18.3432V19H16.3432Z" fill="currentColor" /></svg>
'''

ICON_FORWARD = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M10.5858 6.34317L12 4.92896L19.0711 12L12 19.0711L10.5858 17.6569L16.2427 12L10.5858 6.34317Z" fill="currentColor" /></svg>
'''

ICON_BACKWORD = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M16.2426 6.34317L14.8284 4.92896L7.75739 12L14.8285 19.0711L16.2427 17.6569L10.5858 12L16.2426 6.34317Z" fill="currentColor" /></svg>
'''

ICON_BACKWORD_SKIP = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M16.929 5L18.3432 6.41421L12.6863 12.0711L18.3432 17.7279L16.929 19.1421L9.85789 12.0711L16.929 5Z" fill="currentColor" /><path d="M8 19V5H6V19H8Z" fill="currentColor" /></svg>
'''

ICON_FILE_TEXT = '''
<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" class="bi bi-file-earmark-text" viewBox="0 0 16 16">
  <path d="M5.5 7a.5.5 0 0 0 0 1h5a.5.5 0 0 0 0-1h-5zM5 9.5a.5.5 0 0 1 .5-.5h5a.5.5 0 0 1 0 1h-5a.5.5 0 0 1-.5-.5zm0 2a.5.5 0 0 1 .5-.5h2a.5.5 0 0 1 0 1h-2a.5.5 0 0 1-.5-.5z"/>
  <path d="M9.5 0H4a2 2 0 0 0-2 2v12a2 2 0 0 0 2 2h8a2 2 0 0 0 2-2V4.5L9.5 0zm0 1v2A1.5 1.5 0 0 0 11 4.5h2V14a1 1 0 0 1-1 1H4a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1h5.5z"/>
</svg>
'''

ICON_FILE_TEXT = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M7 18H17V16H7V18Z" fill="currentColor" /><path d="M17 14H7V12H17V14Z" fill="currentColor" /><path d="M7 10H11V8H7V10Z" fill="currentColor" /><path fill-rule="evenodd" clip-rule="evenodd" d="M6 2C4.34315 2 3 3.34315 3 5V19C3 20.6569 4.34315 22 6 22H18C19.6569 22 21 20.6569 21 19V9C21 5.13401 17.866 2 14 2H6ZM6 4H13V9H19V19C19 19.5523 18.5523 20 18 20H6C5.44772 20 5 19.5523 5 19V5C5 4.44772 5.44772 4 6 4ZM15 4.10002C16.6113 4.4271 17.9413 5.52906 18.584 7H15V4.10002Z" fill="currentColor" /></svg>
'''

ICON_PLAYER_PLAY = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path fill-rule="evenodd" clip-rule="evenodd" d="M12 21C16.9706 21 21 16.9706 21 12C21 7.02944 16.9706 3 12 3C7.02944 3 3 7.02944 3 12C3 16.9706 7.02944 21 12 21ZM12 23C18.0751 23 23 18.0751 23 12C23 5.92487 18.0751 1 12 1C5.92487 1 1 5.92487 1 12C1 18.0751 5.92487 23 12 23Z" fill="currentColor" /><path d="M16 12L10 16.3301V7.66987L16 12Z" fill="currentColor" /></svg>
'''

ICON_PLAYER_PAUSE = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M9 9H11V15H9V9Z" fill="currentColor" /><path d="M15 15H13V9H15V15Z" fill="currentColor" /><path fill-rule="evenodd" clip-rule="evenodd" d="M1 5C1 2.79086 2.79086 1 5 1H19C21.2091 1 23 2.79086 23 5V19C23 21.2091 21.2091 23 19 23H5C2.79086 23 1 21.2091 1 19V5ZM5 3H19C20.1046 3 21 3.89543 21 5V19C21 20.1046 20.1046 21 19 21H5C3.89543 21 3 20.1046 3 19V5C3 3.89543 3.89543 3 5 3Z" fill="currentColor" /></svg>
'''

ICON_CONFIIG = '''
<svg class="w-6 h-6" fill="none" stroke="currentColor" viewBox="0 0 24 24" xmlns="http://www.w3.org/2000/svg"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M10.325 4.317c.426-1.756 2.924-1.756 3.35 0a1.724 1.724 0 002.573 1.066c1.543-.94 3.31.826 2.37 2.37a1.724 1.724 0 001.065 2.572c1.756.426 1.756 2.924 0 3.35a1.724 1.724 0 00-1.066 2.573c.94 1.543-.826 3.31-2.37 2.37a1.724 1.724 0 00-2.572 1.065c-.426 1.756-2.924 1.756-3.35 0a1.724 1.724 0 00-2.573-1.066c-1.543.94-3.31-.826-2.37-2.37a1.724 1.724 0 00-1.065-2.572c-1.756-.426-1.756-2.924 0-3.35a1.724 1.724 0 001.066-2.573c-.94-1.543.826-3.31 2.37-2.37.996.608 2.296.07 2.572-1.065z"></path><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 12a3 3 0 11-6 0 3 3 0 016 0z"></path></svg>
'''

ICON_CLOSE = '''
<svg width="24" height="24" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M16.3956 7.75734C16.7862 8.14786 16.7862 8.78103 16.3956 9.17155L13.4142 12.153L16.0896 14.8284C16.4802 15.2189 16.4802 15.8521 16.0896 16.2426C15.6991 16.6331 15.0659 16.6331 14.6754 16.2426L12 13.5672L9.32458 16.2426C8.93405 16.6331 8.30089 16.6331 7.91036 16.2426C7.51984 15.8521 7.51984 15.2189 7.91036 14.8284L10.5858 12.153L7.60436 9.17155C7.21383 8.78103 7.21383 8.14786 7.60436 7.75734C7.99488 7.36681 8.62805 7.36681 9.01857 7.75734L12 10.7388L14.9814 7.75734C15.372 7.36681 16.0051 7.36681 16.3956 7.75734Z" fill="currentColor" /><path fill-rule="evenodd" clip-rule="evenodd" d="M4 1C2.34315 1 1 2.34315 1 4V20C1 21.6569 2.34315 23 4 23H20C21.6569 23 23 21.6569 23 20V4C23 2.34315 21.6569 1 20 1H4ZM20 3H4C3.44772 3 3 3.44772 3 4V20C3 20.5523 3.44772 21 4 21H20C20.5523 21 21 20.5523 21 20V4C21 3.44772 20.5523 3 20 3Z" fill="currentColor" /></svg>
'''

#

Point = collections.namedtuple( 'Point', ['X', 'Y'] )
Point.fromNdarray = lambda x : Point( x[0], x[1] )

DrawFunc = collections.namedtuple( 'DrawFunc', ['f', 'args', 'kwargs'], defaults=( None, (), {} ) )

def makeTkImage( nparray ):

    # important vvv
    # convert skia = BGRA to TkInter = RGBA

    np.dot(
        nparray
    ,   np.array(   [   [0, 0, 1, 0 ]   # 0 <= 2
                    ,   [0, 1, 0, 0 ]   # 1 <= 1
                    ,   [1, 0, 0, 0 ]   # 2 <= 0
                    ,   [0, 0, 0, 1 ]   # 4 <= 4
                    ], dtype = np.uint8
                )
    ,   out = nparray                   # output same array
    )                                   # return same array ( not copy ). So throw it away.

    im = Image.fromarray( nparray, mode="RGBA" )  # make PIL Image

#   ** oops! in-place update is not support
#
#   >>> import numpy as np
#   >>> array = np.array( [ [ 1,2,3,4], [2,4,6,8] ] )
#   >>> array_mtx =  np.array( [ [0, 0, 1, 0 ], [0, 1, 0, 0 ], [1, 0, 0, 0 ], [0, 0, 0, 1 ] ] )
#   >>> array @= array_mtx
#   Traceback (most recent call last):
#     File "<stdin>", line 1, in <module>
#   TypeError: In-place matrix multiplication is not (yet) supported. Use 'a = a @ b' instead of 'a @= b'.
#   >>> array = array @ array_mtx
#   >>> array
#   array([[3, 2, 1, 4],
#          [6, 4, 2, 8]])
#
#   ** oops! in-place another update is very slow...
#
#   t_shape = self.surface.shape
#   t_surface = surface.reshape( [ t_shape[0] * t_shape[1], t_shape[2] ] )
#
#   for i in range( t_surface.shape[ 0 ] ):
#       ( t_surface[i][0], t_surface[i][2] ) = ( t_surface[i][2], t_surface[i][0] )
#
#   im = Image.fromarray( array, mode="RGBA" )
#
#   ** slice is memory copy ...
#
#   im = Image.fromarray( surface[ :, :, [2, 1, 0, 3] ], mode="RGBA" )
#
#   ** This is it !  np.dot( array ... out=array )
#
#   >>> import numpy as np
#   >>>
#   >>> def np_id(x):
#   ...     return x.__array_interface__['data'][0]
#   ...
#   >>> array = np.array( [ [ [ 1,2,3,4], [2,4,6,8] ], [ [ 1,2,3,4], [2,4,6,8] ] ] )
#   >>>
#   >>> i1 = np_id(array)
#   >>>
#   >>> array_mtx =  np.array( [ [0, 0, 1, 0 ], [0, 1, 0, 0 ], [1, 0, 0, 0 ], [0, 0, 0, 1 ] ] )
#   >>> x = np.dot( array, array_mtx, out=array )
#   >>>
#   >>> x
#   array([[[3, 2, 1, 4],
#           [6, 4, 2, 8]],
#
#          [[3, 2, 1, 4],
#           [6, 4, 2, 8]]])
#   >>> array
#   array([[[3, 2, 1, 4],
#           [6, 4, 2, 8]],
#
#          [[3, 2, 1, 4],
#           [6, 4, 2, 8]]])
#   >>>
#   >>> i2 = np_id(x)
#   >>> i3 = np_id(array)
#   >>> ( i1 == i2 == i3 )
#   True

    return ImageTk.PhotoImage( im )      # make TkInter Image

def svgIconRenderer( filename_or_strem, view_w = 16, view_h = 16, color = 0xFF000000 ):

    """
        https://icons.getbootstrap.jp/
        https://css.gg/
        https://heroicons.dev/

        Not all icons on the SVG icon site above have been verified.
        Also, I have not verified any SVG icon sites other than the above.
    """

    re_M    = re.compile( r"matrix\(([^)]*)\)" )
    re_M_P  = re.compile( r"[-+]?(\d+(\.\d*)?|\.\d+)([eE][-+]?\d+)?" )

    re_D = re.compile( r"([MmLlHhVvCcSsQqTtAaZz]|([-+]?(\d+(\.\d*)?|\.\d+)([eE][-+]?\d+)?))" )

    def num_float( str, default = None ):
        ret = default

        try:
            ret = float( str )
        except:
            pass

        return ret

    class handler( xml.sax.handler.ContentHandler ):

        def __init__( self, view_w, view_h, color = 0xFF000000, anti_alias = True ):

            self.color = color
            self.anti_alias = anti_alias
            self.view_w = view_w
            self.view_h = view_h
            self.array = np.zeros( ( view_w, view_h, 4 ), dtype = np.uint8 )
            self.surface = skia.Surface( self.array )
            self.skc = self.surface.getCanvas()
            self.depth = 0
            self.state = 0
            self.svg = False

        def startElement( self, name, attrs ):
            self.depth += 1

            if self.state == 0 and self.depth == 1 and name == "svg":
                self.state = 1

                w = num_float( attrs.get( "width" ), None )
                h = num_float( attrs.get( "height" ), None )
                vbox = attrs.get( "viewBox" )

                if vbox is not None:
                    try:
                        ( _, _, w, h ) = map( lambda x : num_float( x, None ), vbox.split() )
                    except Exception as err:
                        traceback.print_exception( err, file=sys.stderr )

                if self.view_w != w or self.view_h != h:
                    self.skc.scale( self.view_w / w, self.view_h / h )

                self.fill       = attrs.get( "fill" )
                self.stroke     = attrs.get( "stroke" )
                self.s_linecap  = attrs.get( "stroke-linecap" )
                self.s_linejoin = attrs.get( "stroke-linejoin" )
                self.s_width    = attrs.get( "stroke-width" )

            elif self.state == 1 and self.depth == 2:

                # <line x1= y1= x2= y2= ...>
                # <rect x= y= width= height= ...>
                # <polygon points= ...>
                # <circle cx= cy= r= ...>
                # <ellipse cx= cy= rx= ry= ...>
                # <path d= ...>

                if name in ( "path", "rect", "circle", "line", "polygon", "polyline", "ellipse" ):

                    self.skc.save()

                    tr = attrs.get( "transform" )

                    if tr != None:
                        m = re_M.match( tr )

                        if m:
                            param = []

                            for m in re_M_P.finditer( m.group( 1 ) ):

                                param.append( m.group() )

                            if len( param ) >= 6:

                                mtx1 = skia.Matrix.MakeAll(
                                        num_float( param[0] )
                                    ,   num_float( param[1] )
                                    ,   num_float( param[2] )
                                    ,   num_float( param[3] )
                                    ,   num_float( param[4] )
                                    ,   num_float( param[5] )
                                    ,   0
                                    ,   0
                                    ,   1
                                    )

                                mtx2 = self.skc.getTotalMatrix()
                                mtx2.preConcat( mtx1 )

                                self.skc.setMatrix( mtx2 )

                    fr = attrs.get( "fill-rule" )   # fill-rule = "nonzero" or "evenodd"

                    fill        = attrs.get( "fill" )
                    stroke      = attrs.get( "stroke" )
                    s_linecap   = attrs.get( "stroke-linecap" )
                    s_linejoin = attrs.get( "stroke-linejoin" )
                    s_width     = attrs.get( "stroke-width" )

                    if fill is None:
                        fill = self.fill

                    if stroke is None:
                        stroke = self.stroke

                    if s_linecap is None:
                        s_linecap = self.s_linecap

                    if s_linejoin is None:
                        s_linejoin = self.s_linejoin

                    if s_width is None:
                        s_width = self.s_width

                    fill = not ( fill is not None and fill == "none" )
                    stroke = not ( stroke is None or stroke == "none" )

                    param = dict(
                                Color       = self.color
                            ,   AntiAlias   = self.anti_alias
                            )

                    if stroke:

                        if s_linecap == "butt":
                            s_linecap = skia.Paint.kButt_Cap

                        elif s_linecap == "round":
                            s_linecap = skia.Paint.kRound_Cap

                        elif s_linecap == "square":
                            s_linecap = skia.Paint.kSquare_Cap

                        else:
                            s_linecap = None

                        if s_linecap is not None:
                            param[ "StrokeCap" ] = s_linecap

                        if s_linejoin == "miter":
                            s_linejoin = skia.Paint.kMiter_Join

                        elif s_linejoin == "round":
                            s_linejoin = skia.Paint.kRound_Join

                        elif s_linejoin == "bevel":
                            s_linejoin = skia.Paint.kBevel_Join

                        else:
                            s_linejoin = None

                        if s_linejoin is not None:
                            param[ "StrokeJoin" ] = s_linejoin

                        s_width     = num_float( attrs.get( "stroke-width" ), None )

                        if s_width is not None:
                            param[ "StrokeWidth" ] = num_float( s_width, 0 )

                    style = skia.Paint.kFill_Style

                    if stroke and fill:
                        style =  skia.Paint.kStrokeAndFill_Style

                    if stroke and not fill:
                        style =  skia.Paint.kStroke_Style

                    param[ "Style" ] = style

                    paint = skia.Paint( param )

                    if name == "path":

                        d = attrs.get( "d" )

                        if d is not None:

                            path = skia.Path()

                            if fr is not None and fr == "evenodd":
                                path.setFillType( skia.PathFillType.kEvenOdd )

                            def doDrawMoveTo( it ):
                                path.moveTo( next( it ), next( it ) )
                                doDrawLineTo( it )

                            def doDrawRMoveTo( iter ):
                                path.rMoveTo( next( iter ), next( iter ) )
                                doDrawRLineTo( iter )

                            def doDrawLineTo( iter ):
                                while True:
                                    path.lineTo( next( iter ), next( iter ) )

                            def doDrawRLineTo( iter ):
                                while True:
                                    path.rLineTo( next( iter ), next( iter ) )

                            def doDrawLineH( iter ):
                                pt = skia.Point( 0, 0 )
                                if path.countPoints() > 0:
                                    pt = path.getPoint( path.countPoints() - 1 )

                                while True:
                                    x = next( iter )
                                    path.lineTo( x, pt.y() )

                            def doDrawRLineH( iter ):
                                while True:
                                    path.rLineTo( next( iter ), 0 )

                            def doDrawLineV( iter ):
                                pt = skia.Point( 0, 0 )
                                if path.countPoints() > 0:
                                    pt = path.getPoint( path.countPoints() - 1 )

                                while True:
                                    y = next( iter )
                                    path.lineTo( pt.x(), y )

                            def doDrawRLineV( iter ):
                                while True:
                                    path.rLineTo( 0, next( iter ) )

                            def doDrawCubicC( iter ):
                                while True:
                                    path.cubicTo( next( iter ), next( iter ), next( iter ), next( iter ), next( iter ), next( iter ) )

                            def doDrawRCubicC( iter ):
                                while True:
                                    path.rCubicTo( next( iter ), next( iter ), next( iter ), next( iter ), next( iter ), next( iter ) )

                            def doDrawCubicS( iter ):

                                while True:
                                    x2 = next( iter )
                                    y2 = next( iter )
                                    x = next( iter )
                                    y = next( iter )

                                    d1 = skia.Point( 0, 0 )

                                    if path.countVerbs() > 0:
                                        verb = path.getVerbs( path.countVerbs() - 1 )[-1]

                                        d1 = path.getPoint( path.countPoints() - 1 )

                                        if verb == skia.Path.Verb.kCubic_Verb:
                                            d1 *= 2
                                            d1 -= path.getPoint( path.countPoints() - 2 )

                                    path.cubicTo( d1.x(), d1.y(), x2, y2, x, y )

                            def doDrawRCubicS( iter ):

                                while True:

                                    x2 = next( iter )
                                    y2 = next( iter )
                                    x = next( iter )
                                    y = next( iter )

                                    d1 = skia.Point( 0, 0 )

                                    if path.countVerbs() > 0:
                                        verb = path.getVerbs( path.countVerbs() - 1 )[-1]

                                        d1 = path.getPoint( path.countPoints() - 1 )

                                        if verb == skia.Path.Verb.kCubic_Verb:
                                            d1 -= path.getPoint( path.countPoints() - 2 )

                                    path.rCubicTo( d1.x(), d1.y(), x2, y2, x, y )

                            def doDrawQuadQ( iter ):
                                while True:
                                    path.quadTo( next( iter ), next( iter ), next( iter ), next( iter ) )

                            def doDrawRQuadQ( iter ):
                                while True:
                                    path.rQuadTo( next( iter ), next( iter ), next( iter ), next( iter ) )

                            def doDrawQuadT( iter ):

                                while True:
                                    x2 = next( iter )
                                    y2 = next( iter )

                                    d1 = skia.Point( 0, 0 )

                                    if path.countVerbs() > 0:

                                        verb = path.getVerbs( path.countVerbs() - 1 )[-1]

                                        d1 = path.getPoint( path.countPoints() - 1 )

                                        if verb == skia.Path.Verb.kQuad_Verb:
                                            d1 *= 2
                                            d1 -= path.getPoint( path.countPoints() - 2 )

                                    path.quadTo( d1.x(), d1.y(), x1, x2 )

                            def doDrawRQuadT( iter ):

                                while True:
                                    x2 = next( iter )
                                    y2 = next( iter )

                                    d1 = skia.Point( 0, 0 )

                                    if path.countVerbs() > 0:

                                        verb = path.getVerbs( path.countVerbs() - 1 )[-1]

                                        d1 = path.getPoint( path.countPoints() - 1 )

                                        if verb == skia.Path.Verb.kQuad_Verb:
                                            d1 -= path.getPoint( path.countPoints() - 2 )

                                    path.rQuadTo( d1.x(), d1.y(), x1, x2 )

                            def doDrawArc( iter ):
                                while True:

                                    rx          = next( iter )
                                    ry          = next( iter )
                                    xAxisRotate = next( iter )
                                    largeArc    = skia.Path.ArcSize( int( next( iter ) ) )  # : skia.Path.ArcSize,
                                    sweep       = skia.PathDirection.kCCW if int( next( iter ) ) == 0 else skia.PathDirection.kCW   #: skia.PathDirection,
                                    dx          = next( iter )
                                    dy          = next( iter )

                                    path.arcTo( rx, ry, xAxisRotate, largeArc, sweep, dx, dy )

                            def doDrawRArc( iter ):
                                while True:

                                    rx          = next( iter )
                                    ry          = next( iter )
                                    xAxisRotate = next( iter )
                                    largeArc    = skia.Path.ArcSize( int( next( iter ) ) )  # : skia.Path.ArcSize,
                                    sweep       = skia.PathDirection.kCCW if int( next( iter ) ) == 0 else skia.PathDirection.kCW   #: skia.PathDirection,
                                    dx          = next( iter )
                                    dy          = next( iter )

                                    path.rArcTo( rx, ry, xAxisRotate, largeArc, sweep, dx, dy )

                            def doDrawClose( iter ):
                                path.close()
                                next( iter )

                            cmdfunc = {
                                'M' : doDrawMoveTo
                            ,   'm' : doDrawRMoveTo
                            ,   'L' : doDrawLineTo
                            ,   'l' : doDrawRLineTo
                            ,   'H' : doDrawLineH
                            ,   'h' : doDrawRLineH
                            ,   'V' : doDrawLineV
                            ,   'v' : doDrawRLineV
                            ,   'C' : doDrawCubicC
                            ,   'c' : doDrawRCubicC
                            ,   'S' : doDrawCubicS
                            ,   's' : doDrawRCubicS
                            ,   'Q' : doDrawQuadQ
                            ,   'q' : doDrawRQuadQ
                            ,   'T' : doDrawQuadT
                            ,   't' : doDrawRQuadT
                            ,   'A' : doDrawArc
                            ,   'a' : doDrawRArc
                            ,   'Z' : doDrawClose
                            ,   'z' : doDrawClose
                            }

                            class D_Parser:

                                def __init__( self, d ):
                                    self.d = d
                                    self.cmd_c = ""
                                    self.cmd_n = None
                                    self.d_iter = re_D.finditer( d )
                                    self.cmdlist = cmdfunc.keys()

                                def __iter__( self ):
                                    return self

                                def __next__( self ):

                                    class InnerIter:

                                        def __init__( self, parent ):
                                            self.parent = parent
                                            self.a_count = 0
                                            self.a_buffer = []

                                        def __iter__( self ):
                                            return self

                                        def __next__( self ):
                                            if self.parent.cmd_c is None:
                                                raise StopIteration()

                                            if len( self.a_buffer ) > 0:
                                                self.a_count += 1
                                                return num_float( self.a_buffer.pop(0) )

                                            m = next( self.parent.d_iter )

                                            if m.group() in self.parent.cmdlist:
                                                self.parent.cmd_c = None
                                                self.parent.cmd_n = m.group()
                                                raise StopIteration()

                                            if self.parent.cmd_c in ( 'a', 'A' ):

                                                # Process for splitting 'a' and 'A' flags ( Without this it would be simple )
                                                # see https://triple-underscore.github.io/svg-paths-ja.html#PathDataBNF

                                                self.a_count += 1

                                                val = m.group()
                                                ln = len( val )

                                                if ( self.a_count % 7 ) == 4:                   # large-arc-flag

                                                    if ln > 1:
                                                        self.a_buffer.append( val[ 1 ] )

                                                        if ln > 2:
                                                            self.a_buffer.append( val[ 2: ] )

                                                    return num_float( val[ 0 ] )

                                                elif ( self.a_count % 7 ) == 5:                 # sweep-flag

                                                    if ln > 1:
                                                        self.a_buffer.append( val[ 1: ] )

                                                    return num_float( val[ 0 ] )

                                            return num_float( m.group() )

                                    if self.cmd_c is None and self.cmd_n is not None:
                                        self.cmd_c = self.cmd_n
                                        self.cmd_n = None
                                        return ( self.cmd_c, InnerIter( self ) )

                                    while True:
                                        try:
                                            m = next( self.d_iter )

                                        except StopIteration:
                                            self.cmd_c = None
                                            self.cmd_n = None
                                            raise StopIteration()

                                        if m.group() in self.cmdlist:
                                            self.cmd_c = m.group()
                                            self.cmd_n = None
                                            return ( self.cmd_c, InnerIter( self ) )

                                        else:
                                            # skip value
                                            pass

                            for ( cmd, iter ) in D_Parser( d ):
                                try:
                                    cmdfunc[ cmd ]( iter )

                                except StopIteration:
                                    pass

                            self.skc.drawPath( path, paint )

                    elif name == "rect":

                        x = num_float( attrs.get( "x" ) )
                        y = num_float( attrs.get( "y" ) )
                        w = num_float( attrs.get( "width" ) )
                        h = num_float( attrs.get( "height" ) )
                        rx = num_float( attrs.get( "rx" ), 0 )
                        ry = num_float( attrs.get( "ry" ), 0 )

                        if rx == 0 and ry != 0:
                            rx = ry
                        elif ry == 0 and rx != 0:
                            ry = rx

                        self.skc.drawRoundRect( ( x, y, w, h ), rx, ry, paint )

                    elif name == "circle":

                        x = num_float( attrs.get( "cx" ) )
                        y = num_float( attrs.get( "cy" ) )
                        r = num_float( attrs.get( "r" ) )

                        self.skc.drawCircle( x, y, r, paint )

                    else:
                        # name == ( "line", "polygon", "polyline", "ellipse" ) is not fount in bootstrap-icons-1.9.1
                        pass

                    self.skc.restore()
            else:
                self.state = 2

        def endElement( self, name ):
            self.depth -= 1

        def endDocument( self ):
            self.skc.flush()

    h = handler( view_w, view_h, color );
    p = xml.sax.parse( filename_or_strem, h )

    return h.array      # nparray ( view_w, view_h, 4 ), dtype = np.uint8

def format_size( sz ):

    if sz < 1024:
        return "%d bytes" % ( sz, )

    l = [
        ( 2, "kb" )
    ,   ( 3, "MB" )
    ,   ( 4, "GB" )
    ,   ( 5, "TB" )
    ,   ( 6, "PB" )
    ]

    for i in l:
        if sz < math.pow( 1024, i[0] ):
            return "%.2f %s" % ( sz / math.pow( 1024, i[0] - 1 ), i[1] )

    raise Exception()

def format_time_minsec( sec ):

    ( f, i ) = math.modf( sec )

    s = i % 60
    i = ( i - s ) / 60
    m = i % 60

    return "%02d:%02d" % ( m, s )

def format_time( sec ):

    ( f, i ) = math.modf( sec )

    s = i % 60
    i = ( i - s ) / 60
    m = i % 60
    i = ( i - m ) / 60
    h = i % 24
    d = ( i - h ) / 24

    if d == 0:
        return "%02d:%02d:%02d%s" % ( h, m, s, ( "%.2f" % ( f, ) )[-3:] )

    else:
        return "%dd%02d:%02d:%02d%s" % ( d, h, m, s, ( "%.2f" % ( f, ) )[-3:] )


G1code = collections.namedtuple( 'G1code', ( 'X', 'Y', 'Z', 'E', 'F', 'tail', 'cx', 'cy', 'cf', 'no', 'tm', 'tmd' ) )

def parseG1( ln ):

    m = KW_G1.match( ln )

    if m:
        gx = None
        gy = None
        gz = None
        ge = None
        gf = None

        gtail = m.string[ m.end():]

        if gtail == "":
            gtail = None

        for m in KW_G1_PARAM.finditer( m.group( 1 ) ):

            if m:

                try:
                    p = m.group( 1 ).upper()
                    v = float( m.group( 2 ) )

                    if p == 'X':
                        gx = v

                    elif p == 'Y':
                        gy = v

                    elif p == 'Z':
                        gz = v

                    elif p == 'E':
                        ge = v

                    elif p == 'F':
                        gf = v

                except Exception as err:
                    traceback.print_exception( err, file=sys.stderr )

        return G1code( gx, gy, gz, ge, gf, gtail, None, None, None, None, None, None )

    return None

KW_G1         = re.compile( r"\s*G[01]\s+([^;]+)", re.I )
KW_G1_PARAM   = re.compile( r"\s*([A-Z])(-?[0-9.]+)", re.I )

KW_COMMENT          = re.compile( r"^\s*;" )
KW_BED_SHAPE        = re.compile( r"^\s*;\s*bed_shape\s*=\s*(.+)", re.I )
# ; bed_shape = 0x0,250x0,250x210,0x210

KW_EST_PRINT_TIME   = re.compile( r"^\s*;\s*estimated\s*printing\s*time[^=]*=\s*(?:(\d+)d)?\s*(?:(\d+)h)?\s*(?:(\d+)m)?\s*(?:(\d+)s)?", re.I )
# ; estimated printing time (normal mode) = 1d 13h 52m 56s

KW_THUMBNAIL_BEGIN  = re.compile( r"^\s*;\s*thumbnail\s*begin" )
KW_THUMBNAIL_BODY   = re.compile( r"^\s*;\s*(\S+)" )
KW_THUMBNAIL_END    = re.compile( r"^\s*;\s*thumbnail\s*end" )

KW_LAYER_HEIGHT         = re.compile( r"^\s*;\s*layer_height\s*=\s*([\d.]+)" )
KW_FIRST_LAYER_HEIGHT   = re.compile( r"^\s*;\s*first_layer_height\s*=\s*([\d.]+)" )

LayerData = collections.namedtuple( 'LayerData', ( 'height', 'layer' ) )

class GcodeLoader:

    bed_x_min = None
    bed_x_max = None
    bed_y_min = None
    bed_y_max = None

    layer_data      = []
    raw_gcode       = []
    raw_gcode_cm    = []

    feedrates   = []

    time_est    = 0
    time_calc   = 0
    time_diff_rate = 1

    read_bytes = 0
    size_bytes = 0
    read_time_st = 0
    read_time_nw = 0

    thumbnail_image_bytes = None        # png image bytes

    class DummyLock:
        def __enter__(self): return self
        def __exit__(self, exc_type, exc_value, traceback): pass

    lock = DummyLock()

    err  = None

    def getProc( self ):
        with self.lock:
            return ( self.read_bytes, self.size_bytes, self.read_time_nw - self.read_time_st )

    def getThumbnailImage( self ):
        with self.lock:
            return self.thumbnail_image_bytes

    @staticmethod
    def value_correction( z ):
        return round( z, 3 )

    def __init__( self, tlock = False ):

        if tlock:
            self.lock = threading.Lock()

    def load( self, file = None ):

        err  = None

        self.layer_data = []
        self.raw_gcode      = []
        self.raw_gcode_cm   = []

        self.feedrates = []

        self.read_bytes = 0
        self.size_bytes = 0
        self.read_time_st = time.time()
        self.read_time_nw = time.time()

        try:
            self._load_impl( file )
        except Exception as err:
            self.err = err
            raise err

    def _load_impl( self, file = None ):

        if file is None:
            return

        if not hasattr( file, 'read' ):
            fin = open( file, encoding = 'utf8', errors = 'replace' )
        else:
            fin = file

        if fin.seekable():
            fin.seek( 0, io.SEEK_END )

            with self.lock:
                self.size_bytes = fin.tell()

            fin.seek( 0, io.SEEK_SET )

        c_x = 0
        c_y = 0
        c_z = 0
        c_zz = 0
        c_l = 0
        c_f = 0

        f_bed_s     = False
        f_est       = False
        f_thumb     = 0
        thumb       = io.BytesIO()

        layer = []

        feedrates = set()

        no = -1
        tm_calc = 0

        while True:
            ln = fin.readline()

            if ln == "":
                break

            self.raw_gcode.append( ln )

            no += 1

            if fin.seekable():
                with self.lock:
                    self.read_bytes = fin.tell()

            with self.lock:
                self.read_time_nw = time.time()

            ln = ln.rstrip( "\r\n" )

            if KW_COMMENT.match( ln ):

                if f_thumb != 1:
                    self.raw_gcode_cm.append( no )

                else:       # if f_thumb == 1:
                    m = KW_THUMBNAIL_END.match( ln )

                    if m:
                        f_thumb = 2

                        thumb.seek( 0, os.SEEK_END )

                        if thumb.tell() > 0:
                            thumb.seek( 0, os.SEEK_SET )

                            image_bytes = base64.b64decode( thumb.getvalue() )

                            if len( image_bytes ) >= 8 and image_bytes[0:8] == b'\x89PNG\r\n\x1a\n':
                                with self.lock:
                                    self.thumbnail_image_bytes = image_bytes
                    else:
                        m = KW_THUMBNAIL_BODY.match( ln )

                        if m:
                            thumb.write( m.group( 1 ).encode() )

                    continue

                if f_thumb == 0:
                    m = KW_THUMBNAIL_BEGIN.match( ln )

                    if m:
                        f_thumb = 1
                        continue

                if f_bed_s == False:
                    m = KW_BED_SHAPE.match( ln )

                    if m:
                        f_bed_s = True

                        b_x = []
                        b_y = []

                        for xy in m.group( 1 ).split( ',' ):

                            try:
                                xy = xy.split( 'x' )

                                b_x.append( int( xy[0] ) )
                                b_y.append( int( xy[1] ) )

                            except:
                                pass

                        if len( b_x ) > 0 and len( b_y ) > 0:

                            self.bed_x_min = min( b_x )
                            self.bed_x_max = max( b_x )
                            self.bed_y_min = min( b_y )
                            self.bed_y_max = max( b_y )

                        continue

                if f_est == False:
                    m = KW_EST_PRINT_TIME.match( ln )

                    if m:
                        f_est = True

                        def num_int( x ):

                            ret = 0

                            try:
                                ret = int( x )
                            except:
                                pass

                            return ret

                        td = num_int( m.group( 1 ) )
                        th = num_int( m.group( 2 ) )
                        tm = num_int( m.group( 3 ) )
                        ts = num_int( m.group( 4 ) )

                        self.time_est = ( td * 60 * 60 * 24 ) + ( th * 60 * 60 ) + ( tm * 60 ) + ts

                        continue

            else:
                g1 = parseG1( ln )

                if g1 is not None:

                    if g1.Z is not None:
                        c_z = g1.Z

                    if (    ( c_z < c_l )                                   # z lower   ( ex. Start extrude (0.2mm) is higher than first layer (<0.2mm)
                        or  (   c_z > c_l                                   # z higher
                            and (   ( g1.Z is not None and g1.Z < c_zz )    #   z down
                                or  ( g1.E is not None and g1.E > 0 )       #   extrude
                                )
                            )
                        ):

                        self.layer_data.append( LayerData( self.value_correction( c_l ), layer ) )
                        layer = []
                        c_l = c_z

                    if g1.F is not None:
                        c_f = g1.F

                    if g1.X is not None or g1.Y is not None or g1.Z is not None:

                        if g1.E is not None and g1.E > 0:
                            feedrates.add( c_f )

                        x = ( g1.X - c_x )  if g1.X is not None else 0
                        y = ( g1.Y - c_y )  if g1.Y is not None else 0
                        z = ( g1.Z - c_zz ) if g1.Z is not None else 0
                        l = math.sqrt( x * x + y * y + z * z )
                        tmd = l / ( c_f / 60 )
                        tm_calc += tmd

                        layer.append( G1code( g1.X, g1.Y, g1.Z, g1.E, g1.F, g1.tail, c_x, c_y, c_f, no, tm_calc, tmd ) )

                    if g1.X is not None:
                        c_x = g1.X

                    if g1.Y is not None:
                        c_y = g1.Y

                    if g1.Z is not None:
                        c_zz = g1.Z

        if len( layer ) != 0:
            self.layer_data.append( LayerData( self.value_correction( c_l ), layer ) )

        self.time_calc = tm_calc

        if self.time_est != 0 and self.time_calc != 0:
            self.time_diff_rate = self.time_est / self.time_calc

        self.feedrates = sorted( feedrates )

class Viewer:

    option = None
    root = None

    zoom = ZOOM_DEFAULT

    bed_w = DEFAULT_BED_W
    bed_h = DEFAULT_BED_H
    bed_m = DEFAULT_BED_M

    surface = None

    feedrate_color_h_st = 0.125     # HSV Color H Start
    feedrate_color_h_ln = -0.25     # HSV Color H Length

    canv_rect_xy = Point( 1, 1 )
    canv_rect_wh = Point( 2, 2 )

    canv_rect_offset_X = 0.0
    canv_rect_offset_Y = 0.0

    canv_padxy = 8

    gcode = None
    gcode_lns = []
    gcode_fr_map = {}
    gcode_fr_fail = skia.HSVToColor( [ feedrate_color_h_st  * 360, 1, 1 ] )
    gcode_thumbnail = None

    scan_mark = None

    bed_color = 0xff333333
    legend_border_color = 0xff33ff33

    config_padxy = 10

    play_timer_id = None

    play_timer_span_dic = {  # ms, skip
        "Slow"         : ( int( 1000 /  10 ), 1 )
    ,   "Normal"       : ( int( 1000 / 100 ), 1 )
    ,   "Fast"         : ( int( 1000 / 100 ), 5 )
    ,   "VeryFast"     : ( int( 1000 / 100 ), 10 )
    ,   "SupreSpeed"    : ( int( 1000 / 100 ), 20 )
    ,   "UltraSpeed"    : ( int( 1000 / 100 ), 50 )
    ,   "SoundSpeed"     : ( int( 1000 / 100 ), 100 )
    ,   "HeavenlySpeed"  : ( int( 1000 / 100 ), 200 )
    ,   "LightningSpeed" : ( int( 1000 / 100 ), 500 )
    ,   "GodSpeed"       : ( int( 1000 / 100 ), -1 )
    }

    thread_gl = None
    thread_gl_filename  = None
    thread_gl_thread    = None
    thread_gl_th_image  = None
    thread_gl_ptm       = int( 1000 / 8 )

    def __init__( self, **kwargs ):
        self.option = kwargs

    def play_timer_span( self ):
        return self.play_timer_span_dic.get( self.cbo_pl.get() )

    def gcode_ln_min( self ):
        return 1 if len( self.gcode.layer_data ) > 1 else 0

    def gcode_ln_max( self ):
        return len( self.gcode.layer_data ) - 1

    def gcode_li_max( self ):
        try:
            return len( self.gcode.layer_data[ self.gcode_ln() ].layer )
        except IndexError:
            return 0

    def gcode_ln( self ):
        return self.scale_v_value.get()

    def gcode_li( self ):
        return self.scale_h_value.get()

    def gcode_layer( self, ln ):
        try:
            return self.gcode.layer_data[ ln ].layer
        except IndexError:
            return []

    def gcode_layer_height( self, ln ):
        try:
            return self.gcode.layer_data[ ln ].height
        except IndexError:
            return 0

    def gcode_lnli( self, ln, li ):
        layer = self.gcode_layer( ln )

        if len( layer ) == 0:
            return None

        if li < 0:
            li = 0
        elif li >= len( layer ):
            li = len( layer ) - 1

        return layer[ li ]

    def bedOuter( self ):
        return Point( self.bed_w + self.bed_m * 2, self.bed_h + self.bed_m * 2 )

    def drawAreaSize( self ):
        bed_o = self.bedOuter()
        return Point( int( bed_o.X * self.zoom ), int( bed_o.Y * self.zoom ) )

    def canvAreaSize( self ):
        return Point( self.canv_rect_wh.X - self.canv_rect_xy.X, self.canv_rect_wh.Y - self.canv_rect_xy.Y )

    def feedrateColor( self, fr ):
        return self.gcode_fr_map.get( fr, self.gcode_fr_fail )

    def setupGcode( self, gcode, filename = None ):
        title_tail = ""

        if filename is not None:
            # title_tail = " - %s [%s]" % ( os.path.basename( filename ), filename )
            title_tail = " - [%s]" % ( os.path.basename( filename ) )

        self.root.title( SCRIPT_NAME + title_tail)

        self.gcode = gcode

        self.scale_v.configure( from_ = self.gcode_ln_max(), to = self.gcode_ln_min() )
        self.scale_v_value.set( self.gcode_ln_min() )

        self.scale_h.configure( from_ = 0, to = self.gcode_li_max() )
        self.scale_h_value.set( 0 )

        self.gcode_fr_map = {}

        if len( gcode.feedrates ) > 0:
            min_fr = min( gcode.feedrates )
            max_fr = max( gcode.feedrates )
            wid_fr = max_fr - min_fr

            for fr in gcode.feedrates:

                p = ( ( fr - min_fr ) / wid_fr )
                h = self.feedrate_color_h_st + self.feedrate_color_h_ln * p

                if h < 0.0:
                    h += 1.0
                elif h > 1.0:
                    h -= 1.0

                c = skia.HSVToColor( [ h * 360, 1, 1 ] )

                self.gcode_fr_map[ fr ] = c

        self.zoom = ZOOM_DEFAULT

        if self.gcode.bed_x_max is not None:
            self.bed_w = self.gcode.bed_x_max

        if self.gcode.bed_y_max is not None:
            self.bed_h = self.gcode.bed_y_max

        self.gcode_thumbnail = None

        thumbnail_bytes = self.gcode.getThumbnailImage()

        if thumbnail_bytes != None:
            self.gcode_thumbnail = skia.Image.MakeFromEncoded( skia.Data( thumbnail_bytes ) )

    def setupIcons( self ):
        self.icon_zoom_in       = makeTkImage( svgIconRenderer( io.StringIO( ICON_ZOOM_IN ), 24, 24 ) )
        self.icon_zoom_out      = makeTkImage( svgIconRenderer( io.StringIO( ICON_ZOOM_OUT ), 24, 24 ) )
        self.icon_zoom_reset    = makeTkImage( svgIconRenderer( io.StringIO( ICON_ZOOM_RESET ), 24, 24 ) )
        self.icon_up            = makeTkImage( svgIconRenderer( io.StringIO( ICON_UP ), 24, 24 ) )
        self.icon_down          = makeTkImage( svgIconRenderer( io.StringIO( ICON_DOWN ), 24, 24 ) )
        self.icon_forward_skip  = makeTkImage( svgIconRenderer( io.StringIO( ICON_FORWARD_SKIP ), 24, 24 ) )
        self.icon_forward       = makeTkImage( svgIconRenderer( io.StringIO( ICON_FORWARD ), 24, 24 ) )
        self.icon_backword      = makeTkImage( svgIconRenderer( io.StringIO( ICON_BACKWORD ), 24, 24 ) )
        self.icon_backword_skip = makeTkImage( svgIconRenderer( io.StringIO( ICON_BACKWORD_SKIP ), 24, 24 ) )
        self.icon_file_text     = makeTkImage( svgIconRenderer( io.StringIO( ICON_FILE_TEXT ), 24, 24 ) )
        self.icon_player_play   = makeTkImage( svgIconRenderer( io.StringIO( ICON_PLAYER_PLAY ), 24, 24 ) )
        self.icon_player_pause  = makeTkImage( svgIconRenderer( io.StringIO( ICON_PLAYER_PAUSE ), 24, 24 ) )
        self.icon_config        = makeTkImage( svgIconRenderer( io.StringIO( ICON_CONFIIG ), 24, 24 ) )
        self.icon_close         = makeTkImage( svgIconRenderer( io.StringIO( ICON_CLOSE ), 16, 16, color = self.legend_border_color ) )

    def setupWindow( self ):
        self.root.geometry( self.option.get( 'WIN_GEOMETRY', '%dx%d' % ( DEFAULT_WIN_WIDTH, DEFAULT_WIN_HEIGHT ) ) )
        self.root.minsize( DEFAULT_WIN_WIDTH_MIN, DEFAULT_WIN_HEIGHT_MIN )

        # layout

        self.fwin = ttk.Frame( self.root, padding=1 )

        # canvas

        self.canv       = tk.Canvas( self.fwin, bg="#ddd", relief = tk.SUNKEN, takefocus=False, highlightthickness=0 )

        self.canv_image = makeTkImage( np.full( ( 100, 100, 4 ), 255, dtype=np.uint8 ) ) # importnt
        self.canv_image_id = self.canv.create_image( 0, 0, anchor = tk.NW, image= self.canv_image )

        self.bar_v = tk.Scrollbar( self.fwin, orient=tk.VERTICAL )
        self.bar_h = tk.Scrollbar( self.fwin, orient=tk.HORIZONTAL )

        bg = '#%06x' % ( self.bed_color & 0x00ffffff, )
        fg = '#%06x' % ( self.legend_border_color & 0x00ffffff, )

        style = ttk.Style()
        style.configure( "Custom.TCheckbutton", background=bg, foreground=fg, borderwidth=0 )

        # config

        self.config_image = [ None, None, 0, 0 ]  # image, image_id, width, height

        self.config_frame  = tk.Frame( self.canv, bg=bg )

        self.config_close = tk.Canvas( self.config_frame, width = 16, height = 16, bg=bg, highlightthickness=0 )
        self.config_close_id = self.config_close.create_image( 0, 0, image = self.icon_close , anchor=tk.NW )
        self.config_close.pack( anchor = tk.E )

        self.chk_lg_value = tk.IntVar()
        self.chk_lg_value.set( 1 )
        self.chk_lg = ttk.Checkbutton( self.config_frame, text="show legend", style="Custom.TCheckbutton", command = self.onChange_chk_lg, variable=self.chk_lg_value )
        self.chk_lg.pack( anchor=tk.W )

        self.chk_th_value = tk.IntVar()
        self.chk_th_value.set( 1 )
        self.chk_th = ttk.Checkbutton( self.config_frame, text="show thumbnail", style="Custom.TCheckbutton", command = self.onChange_th_lg, variable=self.chk_th_value )
        self.chk_th.pack( anchor=tk.W )

        self.chk_mv_value = tk.IntVar()
        self.chk_mv_value.set( 1 )
        self.chk_mv = ttk.Checkbutton( self.config_frame, text="show move", style="Custom.TCheckbutton", command = self.onChange_chk_mv, variable=self.chk_mv_value )
        self.chk_mv.pack( anchor=tk.W )

        c_frame = tk.Frame( self.config_frame )

        self.cbo_ly = ttk.Combobox( c_frame, state='readonly', width=7, values=[ "None", "Current", "Prev" ], style="Custom.TCombobox" )
        self.cbo_ly.set( self.cbo_ly.cget( "values" )[0] )

        tk.Label( c_frame, text="layer display:", bg=bg, fg=fg ).pack( side = tk.LEFT )
        self.cbo_ly.pack( side = tk.LEFT )

        c_frame.pack( anchor=tk.W )

        self.chk_stop_value = tk.IntVar()
        self.chk_stop_value.set( 0 )
        self.chk_stop  = ttk.Checkbutton( self.config_frame, text="stop layer end", style="Custom.TCheckbutton", variable=self.chk_stop_value )
        self.chk_stop.pack( anchor=tk.W )

        c_frame = tk.Frame( self.config_frame )

        tk.Label( c_frame, text="bed:", bg=bg, fg=fg ).pack( side = tk.LEFT  )

        self.lbl_bed_wh = tk.Label( c_frame, text="250x210", bg=bg, fg=fg )
        self.lbl_bed_wh.pack( side = tk.LEFT )

        c_frame.pack( anchor=tk.W )

        self.config_frame.place_forget()

        # load progress

        self.loadprog_image = [ None, None, 0, 0 ]  # image, image_id, width, height

        self.loadprog_frame = tk.Frame( self.canv, bg=bg )

        self.loadprog_loading_value = tk.StringVar()
        self.loadprog_loading = tk.Label( self.loadprog_frame, textvariable=self.loadprog_loading_value, bg=bg, fg=fg, anchor = tk.W )
        self.loadprog_loading.pack( side = tk.TOP, fill = tk.X )

        self.loadprog_progress_value = tk.IntVar()
        self.loadprog_progress = ttk.Progressbar( self.loadprog_frame, variable=self.loadprog_progress_value, style="Custom.Horizontal.TProgressbar" )
        self.loadprog_progress.pack( side = tk.TOP, fill = tk.X )

        self.loadprog_size_value = tk.StringVar()
        self.loadprog_size = tk.Label( self.loadprog_frame, textvariable=self.loadprog_size_value, bg=bg, fg=fg, anchor = tk.W )
        self.loadprog_size.pack( side = tk.TOP, fill = tk.X )

        self.loadprog_th = tk.Canvas( self.loadprog_frame, bg=bg, relief = tk.SUNKEN, takefocus=False, highlightthickness=0, width=0, height=0  )
        self.loadprog_th.pack( side = tk.TOP )

        self.loadprog_frame.place_forget()

        # scale_v

        frame_v = ttk.Frame( self.fwin, borderwidth = 0 )

        self.scale_v_value = tk.IntVar()
        self.scale_v = ttk.Scale( frame_v, orient=tk.VERTICAL, from_=0, to=0, command=self.onScaleVChange, variable=self.scale_v_value )

        self.btn_u   = ttk.Button( frame_v, image = self.icon_up,   width=3, command = self.onButton_btn_u )
        self.btn_d   = ttk.Button( frame_v, image = self.icon_down, width=3, command = self.onButton_btn_d )

        ttk.Frame( frame_v, height=16 ).pack( side = tk.TOP )
        self.scale_v.pack( side = tk.TOP, fill=tk.Y, expand=True )
        ttk.Frame( frame_v, height=16 ).pack( side = tk.TOP )
        self.btn_u.pack( side = tk.TOP )
        self.btn_d.pack( side = tk.TOP )

        # scale_h

        frame_h = ttk.Frame( self.fwin, borderwidth = 0 )

        self.scale_h_value = tk.IntVar()
        self.scale_h = ttk.Scale( frame_h, orient=tk.HORIZONTAL, from_=0, to=0, command=self.onScaleHChange, variable=self.scale_h_value )

        self.btn_pp  = ttk.Button( frame_h, image = self.icon_backword_skip,  width=3, command = self.onButton_btn_pp )
        self.btn_p   = ttk.Button( frame_h, image = self.icon_backword,       width=3, command = self.onButton_btn_p )
        self.btn_n   = ttk.Button( frame_h, image = self.icon_forward,        width=3, command = self.onButton_btn_n )
        self.btn_nn  = ttk.Button( frame_h, image = self.icon_forward_skip,   width=3, command = self.onButton_btn_nn )

        ttk.Frame( frame_h, width=8).pack( side = tk.LEFT )
        self.scale_h.pack( side = tk.LEFT, fill=tk.X, expand=True )
        ttk.Frame( frame_h, width=8).pack( side = tk.LEFT )

        self.btn_pp.pack( side = tk.LEFT )
        self.btn_p.pack( side = tk.LEFT )
        self.btn_n.pack( side = tk.LEFT )
        self.btn_nn.pack( side = tk.LEFT)

        self.bar_v.set( 0, 1 )
        self.bar_h.set( 0, 1 )
        self.bar_v.config( command = functools.partial( self.onBarChange, self.bar_v ) )
        self.bar_h.config( command = functools.partial( self.onBarChange, self.bar_h ) )

        self.canv.grid( column=0, row=0, sticky=( tk.N, tk.S, tk.E, tk.W ) )
        self.bar_v.grid( column=1, row=0, sticky=( tk.N, tk.S ) )
        self.bar_h.grid( column=0, row=1, sticky=( tk.E, tk.W ) )
        frame_v.grid( column=2, row=0, sticky=( tk.N, tk.S ) )
        frame_h.grid( column=0, row=2, columnspan=3, sticky=( tk.E, tk.W ) )

        self.fwin.grid_columnconfigure(0, weight=1)
        self.fwin.grid_rowconfigure(0, weight=1)

        # status bar

        self.stat_bar = ttk.Frame( self.root, borderwidth = 2, relief = tk.SUNKEN )
        self.label  = ttk.Label( self.stat_bar, anchor = tk.W, text="", relief="ridge", padding=( 6,0 ) )

        self.lbl_zm  = ttk.Label( self.stat_bar, text="", width=7, relief="ridge", anchor = tk.CENTER )

        self.btn_zi = ttk.Button( self.stat_bar, image = self.icon_zoom_in,     width=3, command = self.onButton_btn_zi )
        self.btn_zo = ttk.Button( self.stat_bar, image = self.icon_zoom_out,    width=3, command = self.onButton_btn_zo )
        self.btn_zr = ttk.Button( self.stat_bar, image = self.icon_zoom_reset,  width=3, command = self.onButton_btn_zr )

        self.btn_pl = ttk.Button( self.stat_bar, width=3, command = self.onButton_btn_pl )
        self.updatePlayState( False )

        self.cbo_pl = ttk.Combobox( self.stat_bar, state='readonly'
            ,   width = max( map( lambda x : len( x ), self.play_timer_span_dic.keys() ) )
            ,   values = tuple( self.play_timer_span_dic.keys() )
            )
        self.cbo_pl.set( self.cbo_pl.cget( "values" )[1] )

        self.btn_cfg = ttk.Button( self.stat_bar, image = self.icon_config, width=3, command = self.onButton_btn_cfg )
        self.btn_op = ttk.Button( self.stat_bar, image=self.icon_file_text, width=5, command = self.onButton_btn_open )

        ttk.Frame( self.stat_bar, width=6 ).pack( side = tk.LEFT )
        self.label.pack( side = tk.LEFT, fill=tk.X, expand=True )

        ttk.Frame( self.stat_bar, width=8).pack( side = tk.LEFT )
        self.lbl_zm.pack( side = tk.LEFT )
        self.btn_zi.pack( side = tk.LEFT )
        self.btn_zo.pack( side = tk.LEFT )
        self.btn_zr.pack( side = tk.LEFT )

        ttk.Frame( self.stat_bar, width=8).pack( side = tk.LEFT )
        self.btn_pl.pack( side = tk.LEFT )
        ttk.Label( self.stat_bar, text="speed:" ).pack( side = tk.LEFT )
        self.cbo_pl.pack( side = tk.LEFT )

        ttk.Frame( self.stat_bar, width=8).pack( side = tk.LEFT )
        self.btn_cfg.pack( side = tk.LEFT )

        ttk.Frame( self.stat_bar, width=8).pack( side = tk.LEFT )
        self.btn_op.pack( side = tk.LEFT )
        ttk.Frame( self.stat_bar, width=8).pack( side = tk.LEFT )

        ttk.Sizegrip( self.stat_bar ).pack( side = tk.RIGHT, fill=tk.Y )

        self.stat_bar.pack( side = tk.BOTTOM, fill=tk.X )
        self.fwin.pack( side = tk.BOTTOM, fill=tk.BOTH, expand=True )

        # event bind

        self.canv.bind( "<Configure>",          self.onResize )
        self.canv.bind( "<ButtonPress-1>",      self.scrollStart )
        self.canv.bind( "<B1-Motion>",          self.scrollMove )
        self.canv.bind( "<ButtonRelease-1>",    self.scrollEnd )
        self.canv.bind( "<MouseWheel>",         self.zoomInOut )

        self.config_frame.bind( "<Configure>", self.onResizeConfig )
        self.config_frame.bind( "<Visibility>", self.onResizeConfig )

        self.loadprog_frame.bind( "<Configure>", self.onResizeConfig )
        self.loadprog_frame.bind( "<Visibility>", self.onResizeConfig )

        self.cbo_ly.bind( "<<ComboboxSelected>>", self.onChange_cbo_ly )

        self.config_close.tag_bind( self.config_close_id, "<ButtonPress-1>", self.onButton_config_close  )

        self.root.drop_target_register( tkdnd.DND_FILES )
        self.root.dnd_bind( '<<Drop>>', self.onDropFile )

    def onResize( self, event ):
        self.canv_rect_xy = Point( event.x, event.y )
        self.canv_rect_wh = Point( event.width, event.height )

        self.updateScrollBar()
        self.updateImage()

        if self.config_frame.winfo_ismapped():
            x = self.canv.winfo_width() - self.config_padxy
            y = self.canv.winfo_height() - self.config_padxy

            self.config_frame.place( x=x, y=y, anchor = tk.SE )

        self.configReposition()
        self.loadProgressReposition()

    def onResizeConfig( self, event ):
        target = event.widget
        target_image = None

        if target == self.config_frame:
            target_image = self.config_image

        elif target == self.loadprog_frame:
            target_image = self.loadprog_image

        x = target.winfo_x() - self.config_padxy
        y = target.winfo_y() - self.config_padxy
        w = target.winfo_width() + self.config_padxy * 2
        h = target.winfo_height() + self.config_padxy * 2

        if target_image[ 1 ] is None:
            target_image[ 1 ] = self.canv.create_image( 0, 0, anchor=tk.NW )

        if target_image[ 0 ] is None or target_image[ 2 ] != w or target_image[ 3 ] != h:
            surface = np.zeros( ( h, w, 4 ), dtype = np.uint8 )

            with skia.Surface( surface ) as skc:
                l0 = skia.Paint( Color=self.bed_color, AntiAlias=True )
                l1 = skia.Paint( Color=self.legend_border_color, AntiAlias=True, StrokeWidth=2, Style=skia.Paint.kStroke_Style )

                rect = skia.Rect.MakeWH( w, h )

                skc.drawRoundRect( rect, 10, 10, l0 )
                skc.drawRoundRect( rect.makeInset( 2, 2 ), 10, 10, l1 )

            target_image[ 0 ] = makeTkImage( surface )
            target_image[ 2 ] = w
            target_image[ 3 ] = h

            self.canv.itemconfig( target_image[ 1 ], image = target_image[ 0 ] )
            self.canv.moveto( target_image[ 1 ], x, y )
            self.canv.lift( target_image[ 1 ], self.canv_image_id )

        else:
            self.canv.moveto( target_image[ 1 ], x, y )

    def setupCanvasImage( self ):

        # important ^^^

        # important vvv
        # Reference the object to an instance of the class,
        # since the object has already been deleted when the actual drawing takes place

        self.canv_image = makeTkImage( self.surface )

        # important ^^^

        self.canv.itemconfig( self.canv_image_id, image = self.canv_image )

        # label update

        g1 = self.gcode_lnli( self.gcode_ln(), self.gcode_li() )

        msg = ""

        if g1 is not None:
            msg = "FR:%.1f TM:%s Lno:%d" % ( g1.cf / 60, format_time( g1.tm * self.gcode.time_diff_rate ) , g1.no + 1 )

        msg = "L:%d/%d (%.2fmm/%.2fmm) I:%d/%d %s" % (
                    self.gcode_ln(), self.gcode_ln_max()
                ,   self.gcode_layer_height( self.gcode_ln() )
                ,   self.gcode_layer_height( -1 )
                ,   self.gcode_li() + 1, self.gcode_li_max() + 1
                ,   msg
                )

        self.label.configure( text = msg )

        msg = "x %4.2f" % ( self.zoom / ZOOM_DEFAULT, )
        self.lbl_zm.configure( text = msg )

        msg = "%3dx%3d" % ( self.bed_w, self.bed_h )
        self.lbl_bed_wh.configure( text = msg )

    def onBarChange( self, target, command, *args ):
        ( first, last ) = target.get()

        delta = 0

        if command == 'moveto':
            delta = float( args[0] ) - first

        elif command == 'scroll':
            by = 0

            if args[1] == 'pages':
                by = 0.1

            elif args[1] == 'units':
                by = 0.01

            delta = ( first + ( 1 - last ) ) * by * int( args[0] )

        first += delta
        last  += delta

        delta = 0

        if first <= 0.0:
            delta = 0 - first

        if last >= 1.0:
            delta = 1 - last

        first += delta
        last  += delta

        target.set( first, last )

        self.updateImage()

    def updateScrollBar( self ):
        canv_wh = self.canvAreaSize()
        draw_wh = self.drawAreaSize()

        for ( target, new_last )  in (
                ( self.bar_h, canv_wh.X / draw_wh.X )
            ,   ( self.bar_v, canv_wh.Y / draw_wh.Y )
            ):
            ( old_first, old_last ) = target.get()

            new_first = 0

            if new_last < 1.0:

                old_center = ( old_first + old_last ) / 2

                delta = ( 1.0 - new_last ) * old_center

                new_first += delta
                new_last  += delta

                delta = 0

                if new_first <= 0.0:
                    delta = 0 - new_first

                if new_last >= 1.0:
                    delta = 1 - new_last

                new_first += delta
                new_last  += delta

            else:
                new_first = 0
                new_last  = 1

            target.set( new_first, new_last )

    def updateImage( self ):
        canv_wh = self.canvAreaSize()

        if self.surface is None or self.surface.shape != ( canv_wh.Y, canv_wh.X, 4 ):
            self.surface = np.zeros( ( canv_wh.Y, canv_wh.X, 4 ), dtype = np.uint8 )   # Remake surface

        bed_o = self.bedOuter()
        bed_t = Point( self.bed_w, self.bed_h )
        bed_h = Point( self.bed_m, self.bed_m )

        draw_wh = self.drawAreaSize()

        ( h_offset_f, h_offset_l ) = self.bar_h.get()
        ( v_offset_f, v_offset_l ) = self.bar_v.get()

        with skia.Surface( self.surface ) as skc:
            # matrix setup
            mtx = matrix_tran( 0, 0 )

            for _mtx in (
                    matrix_scale( self.zoom, -self.zoom )
                ,   matrix_tran( bed_h.X * self.zoom, canv_wh.Y - bed_h.Y * self.zoom )
                ,   matrix_tran( -draw_wh.X * h_offset_f, draw_wh.Y * ( 1 - v_offset_l )  )
                ,   matrix_tran(
                        ( canv_wh.X - draw_wh.X ) / 2 * ( 1 if ( h_offset_l - h_offset_f ) == 1 else 0 )
                    ,   -( canv_wh.Y - draw_wh.Y ) / 2 * ( 1 if ( v_offset_l - v_offset_f ) == 1 else 0 )
                    )
                ):
                mtx = np.dot( _mtx, mtx )

            def coordXY( x, y = None ):
                if y is None:
                    return coordXY( x[0], x[1] )

                return Point.fromNdarray( np.dot( mtx, np.array( ( x, y, 1 ) ) ) )

            # clear

            skc.clear( 0x00000000 )

            # bed grid draw

            skc.save()

            skc.translate( 0, 0 )
            skc.scale( 1, 1 )

            a0 = skia.Paint( Color=self.bed_color, AntiAlias=True )

            a1 = skia.Paint( Color=0xff33ff33, AntiAlias=False, StrokeWidth=2, Style=skia.Paint.kStroke_Style )

            a2 = skia.Paint( Color=0xff33ff33, AntiAlias=True )
            f2 = skia.Font( None, 13.5 if self.zoom >= ZOOM_DEFAULT else 13.5 * self.zoom / ZOOM_DEFAULT )

            a3 = skia.Paint( Color=0xffaaaaaa, AntiAlias=False, StrokeWidth=1, Style=skia.Paint.kStroke_Style )

            p0 = coordXY( self.bed_m * -1, bed_t.Y + self.bed_m )
            p1 = coordXY( bed_t.X + self.bed_m, self.bed_m * -1 )

            bed_rect = skia.Rect.MakeXYWH( p0.X, p0.Y, p1.X - p0.X, p1.Y - p0.Y )

            skc.clipRect( bed_rect )
            skc.drawRoundRect( bed_rect, 10, 10, a0 )

            p0 = coordXY( self.bed_m * -1, 0 )
            p1 = coordXY( bed_t.X + self.bed_m, 0 )
            skc.drawLine( p0, p1, a1 )

            p0 = coordXY( 0, self.bed_m * -1 )
            p1 = coordXY( 0, bed_t.Y + self.bed_m )
            skc.drawLine( p0, p1, a1 )

            fh  = f2.getSpacing()
            fw0 = f2.measureText( '0' )

            p0 = coordXY( 0, 0 )
            skc.drawString( "0", p0.X - fw0 * 1.2, p0.Y + fh * 0.75, f2, a2 )

            tick = list( range( 50, bed_t.X, 50 ) )

            if tick[-1] != bed_t.X:
                tick.append( bed_t.X )

            for t in tick:

                p0 = coordXY( t, 0 )
                p1 = coordXY( t, bed_t.Y )
                skc.drawLine( p0, p1, a3 )

                fwt = f2.measureText( str( t ) )
                skc.drawString( str( t ), p0.X - fwt - fw0 * 0.4, p0.Y + fh * 0.75, f2, a2 )

            tick = list( range( 50, bed_t.Y, 50 ) )

            if tick[-1] != bed_t.Y:
                tick.append( bed_t.Y )

            for t in tick:

                p0 = coordXY( 0, t )
                p1 = coordXY( bed_t.X, t )
                skc.drawLine( p0, p1, a3 )

                fwt = f2.measureText( str( t ) )
                skc.drawString( str( t ), p0.X - fwt - fw0 * 0.4, p0.Y + fh * 0.75, f2, a2 )

            skc.restore()

            # move draw prepair

            cr    = 5
            pa_e  = functools.partial( skia.Paint
                        ,   Color=0xff990000
                        ,   AntiAlias=True
                        ,   StrokeWidth=0.4
                        ,   Style=skia.Paint.kStroke_Style
                        ,   StrokeCap=skia.Paint.kRound_Cap
                        ,   StrokeJoin=skia.Paint.kRound_Join
                        )
            pa_e_b_color = 0xcc666666

            pa_m  = skia.Paint( Color=0xff00cc00, AntiAlias=True, StrokeWidth=1.0, Style=skia.Paint.kStroke_Style )
            pa_zu = skia.Paint( Color=0xff00ff00, AntiAlias=True )
            pa_zd = skia.Paint( Color=0xffffffff, AntiAlias=True )

            d_layer_0   = []    # Use canvas affine transformation
            d_layer_1   = []    # Use custom affine transformation

            # prepair current or prev layer

            d_layer_b_opt = self.cbo_ly.get()
            d_layer_b_ln = 0 if d_layer_b_opt == "Current" else -1 if d_layer_b_opt == "Prev" else None

            d_point     = []    # [0] : feedrate, [1:] Point

            def d_point_func_b( feedrate = None ):
                if len( d_point ) > 0:
                    if feedrate is None or feedrate != d_point[ 0 ]:
                        d_layer_0.append( DrawFunc( skc.drawPoints, ( skia.Canvas.PointMode.kPolygon_PointMode, d_point[1:], pa_e( Color = pa_e_b_color ) ) )
                        )
                        d_point.clear()

            if d_layer_b_ln is not None:
                layer_b = self.gcode_layer( self.gcode_ln() + d_layer_b_ln )

                for g1 in layer_b:

                    if g1.Z is None:
                        x = g1.X if g1.X is not None else g1.cx
                        y = g1.Y if g1.Y is not None else g1.cy

                        if g1.E is not None and g1.E > 0:

                            d_point_func_b( g1.cf )

                            if len( d_point ) == 0:
                                d_point.append( g1.cf )
                                d_point.append( Point( g1.cx, g1.cy ) )

                            d_point.append( Point( x, y ) )
                            continue

                    d_point_func_b()

                d_point_func_b()

            # prepair current move

            d_point     = []    # [0] : feedrate, [1:] Point

            layer_h = self.gcode_layer_height( self.gcode_ln() )
            layer   = self.gcode_layer( self.gcode_ln() )

            def d_point_func( feedrate = None ):
                if len( d_point ) > 0:
                    if feedrate is None or feedrate != d_point[ 0 ]:
                        d_layer_0.append( DrawFunc( skc.drawPoints, ( skia.Canvas.PointMode.kPolygon_PointMode, tuple( d_point[1:] ), pa_e( Color = self.feedrateColor( d_point[ 0 ] ) ) ) ) )
                        d_point.clear()

            for i in range( min( self.gcode_li() + 1, len( layer ) ) ):
                g1 = layer[ i ]

                if g1.Z is not None:
                    d_point_func()

                    x = g1.X if g1.X is not None else g1.cx
                    y = g1.Y if g1.Y is not None else g1.cy

                    if x != g1.cx or y != g1.cy:
                        d_layer_1.append( DrawFunc( skc.drawLine, ( coordXY( g1.cx, g1.cy ), coordXY( x, y ), pa_e() if g1.E is not None and g1.E > 0 else pa_e() ) ) )

                    d_layer_1.append( DrawFunc( skc.drawCircle, ( coordXY( x, y ), cr, pa_zu if g1.Z > layer_h else pa_zd ) ) )

                else:
                    x = g1.X if g1.X is not None else g1.cx
                    y = g1.Y if g1.Y is not None else g1.cy

                    if g1.E is not None and g1.E > 0:

                        d_point_func( g1.cf )

                        if len( d_point ) == 0:
                            d_point.append( g1.cf )
                            d_point.append( Point( g1.cx, g1.cy ) )

                        d_point.append( Point( x, y ) )
                        # d_layer_0.append( DrawFunc( skc.drawLine, ( Point( g1.cx, g1.cy ), Point( x, y ), pa_e ) ) )

                    else:
                        d_point_func()
                        d_layer_1.append( DrawFunc( skc.drawLine, ( coordXY( g1.cx, g1.cy ), coordXY( x, y ), pa_m ) ) )

            d_point_func()

            # move draw ( d_layer_0 )

            skc.save()

            skc.setMatrix( skia.Matrix( mtx ) )

            for x in d_layer_0:
                x[0]( *x[1], **x[2] )

            skc.restore()

            # move draw ( d_layer_1 )

            if self.chk_mv_value.get() == 1:
                skc.save()
                skc.setMatrix( skia.Matrix() )

                for x in d_layer_1:
                    x[0]( *x[1], **x[2] )

                skc.restore()

            # legend

            l0 = skia.Paint( Color=self.bed_color, AntiAlias=True )
            l1 = skia.Paint( Color=self.legend_border_color, AntiAlias=True, StrokeWidth=2, Style=skia.Paint.kStroke_Style )

            l2 = skia.Paint( Color=0xff33ff33, AntiAlias=True )
            lf2 = skia.Font( None, 13.5 )

            l3 = functools.partial( skia.Paint, Color=0xff333333, AntiAlias=True )

            if self.chk_lg_value.get() != 0:

                # prepair
                hf_e = 1 if len( self.gcode_fr_map ) > 0 else 0
                mv_e = 3 if self.chk_mv_value.get() == 1 else 0

                h  = len( self.gcode_fr_map ) + hf_e + mv_e
                dh = lf2.getSize()
                t_offset = 1.3

                ww = 15

                fr_fmt0 = "%.1f : "
                fr_fmt1 = "%d"

                wmax0 = 0
                wmax1 = 0

                frs = list( self.gcode_fr_map.keys() )

                if len( self.gcode_fr_map ) != 0:
                    wmax0 = max( map( lambda fr : lf2.measureText( fr_fmt0 % ( fr / 60, ) ), frs) )
                    wmax1 = max( map( lambda fr : lf2.measureText( fr_fmt1 % ( fr, ) ), frs  ) )

                wmax0 = max( wmax0, lf2.measureText( "mm/s : " ) )
                wmax1 = max( wmax1, lf2.measureText( "mm/m" ) )

                cx1 = 10
                cx2 = 30

                wmax2 = cx1 + cx2 + max( wmax0 + wmax1, lf2.measureText( "z-down" ) )

                # draw

                skc.save()

                skc.translate( self.canv_padxy, self.canv_padxy )

                legend_rect = skia.Rect.MakeWH( wmax2, ( h + 1 ) * dh  )

                skc.clipRect( legend_rect )
                skc.drawRoundRect( legend_rect, 10, 10, l0 )
                skc.drawRoundRect( legend_rect.makeInset( 2, 2 ), 10, 10, l1 )

                i = 0

                if hf_e > 0:
                    txt = "mm/s : "
                    p0 = Point( cx2 + ( wmax0 ) - lf2.measureText( txt ) , ( i + t_offset  ) * dh )
                    skc.drawString( txt, p0.X, p0.Y, lf2, l2 )

                    txt = "mm/m"
                    p0 = Point( cx2 + ( wmax0 + wmax1 ) - lf2.measureText( txt ) , ( i + t_offset  ) * dh )
                    skc.drawString( txt, p0.X, p0.Y, lf2, l2 )
                    i += 1

                for fr, clr in self.gcode_fr_map.items():
                    txt = fr_fmt0 % ( fr / 60, )
                    p0 = Point( cx2 + ( wmax0 ) - lf2.measureText( txt ) , ( i + t_offset  ) * dh )
                    skc.drawString( txt, p0.X, p0.Y, lf2, l2 )

                    txt = fr_fmt1 % ( fr, )
                    p0 = Point( cx2 + ( wmax0 + wmax1 ) - lf2.measureText( txt ) , ( i + t_offset  ) * dh )
                    skc.drawString( txt, p0.X, p0.Y, lf2, l2 )

                    r = skia.Rect.MakeXYWH( cx1, ( i + t_offset - 0.5 ) * dh , ww, dh * 0.3 )
                    skc.drawRoundRect( r, 5, 5, l3( Color=clr ) )
                    i += 1

                if mv_e > 0:
                    p0 = Point( cx2, ( i + t_offset  ) * dh )
                    skc.drawString( "move", p0.X, p0.Y, lf2, l2 )
                    p0 = Point( cx1, ( i + t_offset - 0.3 ) * dh )
                    skc.drawLine( p0.X, p0.Y, p0.X + ww, p0.Y, pa_m )
                    i += 1

                    p0 = Point( cx2, ( i + t_offset  ) * dh )
                    skc.drawString( "z-up", p0.X, p0.Y, lf2, l2 )
                    p0 = Point( cx1, ( i + t_offset - 0.3 ) * dh )
                    skc.drawCircle( p0.X + ( ww / 2 ), p0.Y, cr, pa_zu )
                    i += 1

                    p0 = Point( cx2, ( i + t_offset  ) * dh )
                    skc.drawString( "z-down", p0.X, p0.Y, lf2, l2 )
                    p0 = Point( cx1, ( i + t_offset - 0.3 ) * dh )
                    skc.drawCircle( p0.X + ( ww / 2 ), p0.Y, cr, pa_zd )
                    i += 1

                skc.restore()

            if self.chk_th_value.get() != 0:

                skc.save()

                w = 50
                h = 50

                ipad = 6

                if self.gcode_thumbnail != None:
                    w = self.gcode_thumbnail.width()
                    h = self.gcode_thumbnail.height()

                skc.translate( canv_wh.X - w - self.canv_padxy - ipad * 2, self.canv_padxy  )

                rect = skia.Rect.MakeWH( w + ipad * 2, h + ipad * 2 )

                skc.save()
                skc.clipRect( rect )
                skc.drawRoundRect( rect, 10, 10, l0 )
                skc.drawRoundRect( rect.makeInset( 2, 2 ), 10, 10, l1 )
                skc.restore()

                if self.gcode_thumbnail != None:
                    rect = rect.makeInset( ipad, ipad )

                    skc.save()
                    skc.clipRect( rect )
                    skc.drawImageRect( self.gcode_thumbnail, rect )
                    skc.restore()

        self.setupCanvasImage()

    def scrollStart( self, event ):
        self.scan_mark = Point( event.x, event.y )
        event.widget.config( cursor="fleur" )

    def scrollMove( self, event ):
        if self.scan_mark is not None:

            canv_wh = self.canvAreaSize()
            draw_wh = self.drawAreaSize()

            for ( target, delta )  in (
                    ( self.bar_h, ( event.x - self.scan_mark.X ) / draw_wh.X )
                ,   ( self.bar_v, ( event.y - self.scan_mark.Y ) / draw_wh.Y )
                ):
                ( first, last ) = target.get()

                if not ( first == 0 and last == 1 ):
                    first -= delta
                    last -= delta

                    delta = 0

                    if first <= 0.0:
                        delta = 0 - first

                    if last >= 1.0:
                        delta = 1 - last

                    first += delta
                    last  += delta

                    target.set( first, last )

                    self.updateImage()

            self.scan_mark = Point( event.x, event.y )

    def scrollEnd( self, event ):
        event.widget.config( cursor="" )
        self.scan_mark = None

    def zoomInOut( self, event ):
        canv_wh = self.canvAreaSize()
        draw_wh = self.drawAreaSize()

        zoom = self.zoom

        if event.delta > 0 and self.zoom  < ZOOM_MAX:
            zoom += ZOOM_TICK

        elif event.delta < 0 and self.zoom > ZOOM_MIN:
            zoom -= ZOOM_TICK

        if zoom != self.zoom:
            self.zoom = zoom
            self.updateScrollBar()
            self.updateImage()

    def isConfigVisible( self ):
        return self.config_frame.winfo_ismapped()

    def configReposition( self, force = None ):
        if force or self.isConfigVisible():
            x = self.canv.winfo_width() - self.config_padxy - self.canv_padxy
            y = self.canv.winfo_height() - self.config_padxy - self.canv_padxy

            self.config_frame.place( x=x, y=y, anchor = tk.SE )

    def showConfig( self, show ):
        if show:
            self.configReposition( True )

        else:
            self.config_frame.place_forget()
            self.canv.delete( self.config_image[ 1 ] )
            self.config_image = [ None, None, 0, 0 ]

        self.canv.update()

    def loadProgressReposition( self, force = None ):
        if force or self.loadprog_frame.winfo_ismapped():

            x = self.canv.winfo_width() / 2
            y = self.canv.winfo_height() / 2

            self.loadprog_frame.place( x=x, y=y, anchor = tk.CENTER )

    def showLoadProgress( self, filename ):
        self.loadProgressReposition( True )

    def hideLoadProgress( self ):
        self.loadprog_frame.place_forget()
        self.canv.delete( self.loadprog_image[ 1 ] )
        self.loadprog_image = [ None, None, 0, 0 ]

    def onButton_config_close( self, event = None ):
        if self.isConfigVisible():
            self.showConfig( False )

    def onButton_btn_cfg( self, event = None ):
        if self.isConfigVisible():
            self.showConfig( False )
        else:
            self.showConfig( True )

    EventWithDelta = collections.namedtuple( 'EventWithDelta', ['delta',] )

    def onButton_btn_zi( self, event = None ):
        self.zoomInOut( self.EventWithDelta( 1 ) )

    def onButton_btn_zo( self, event = None ):
        self.zoomInOut( self.EventWithDelta( -1 ) )

    def onButton_btn_zr( self, event = None ):
        self.zoom = ZOOM_DEFAULT
        self.updateScrollBar()
        self.updateImage()

    def onScaleVChange( self, event ):
        old_value = self.scale_v_value.get()

        value = int( round( float( event ) ) )
        value = min( max( self.gcode_ln_min(), value ), self.gcode_ln_max() )

        self.scale_v_value.set( value )

        self.scale_h.configure( from_ = 0, to = self.gcode_li_max() )
        self.scale_h_value.set( self.gcode_li_max() )

        self.updateImage()

    def onScaleHChange( self, event ):
        old_value = self.scale_h_value.get()

        value = round( float( event ) )
        value = min( max( 0, value ), self.gcode_li_max() )

        self.scale_h_value.set( value )

        self.updateImage()

    def onChange_chk_lg( self, event = None ):
        self.updateImage()

    def onChange_th_lg( self, event = None ):
        self.updateImage()

    def onChange_chk_mv( self, event = None ):
        self.updateImage()

    def onChange_cbo_ly( self, event = None ):
        self.updateImage()

    def updatePlayState( self, force = None ):
        if self.thread_gl_thread is not None:
            force = False

        if force is not None and ( self.play_timer_id is not None ) != force:
            if force:

                ( ms, skip ) = self.play_timer_span()
                self.play_timer_id = self.root.after( ms, self.progressPlay )

            else:
                self.root.after_cancel( self.play_timer_id )
                self.play_timer_id = None

        self.btn_pl.configure( image =  self.icon_player_play if self.play_timer_id is None else self.icon_player_pause )

    def progressPlay( self ):
        if self.play_timer_id is not None:

            if( self.gcode_li() == self.gcode_li_max()
                and ( self.gcode_ln() == self.gcode_ln_max() or self.chk_stop_value.get() != 0 )
                ):
                self.updatePlayState( False )
            else:
                ( ms, skip ) = self.play_timer_span()

                if skip == -1:
                    if  self.gcode_li() == self.gcode_li_max():
                        self.layerUp( True )

                    self.scale_h_value.set( self.gcode_li_max() )

                elif skip == 1:
                    self.onButton_btn_n()

                elif self.gcode_li() == self.gcode_li_max():
                    self.layerUp( True )

                else:

                    li_max = self.gcode_li_max()
                    li_cur = self.scale_h_value.get()

                    layer = self.gcode_layer( self.gcode_ln() )

                    while skip > 0 and li_cur < li_max:

                        li_cur += 1

                        g1 = layer[ li_cur ]

                        if g1.E is not None and g1.E > 0:
                            skip -= 1

                    self.scale_h_value.set( min( li_cur, li_max ) )

                self.updateImage()

                self.play_timer_id = self.root.after( ms, self.progressPlay )

    def onButton_btn_pl( self, event = None ):
        if self.play_timer_id is None and self.gcode_li() == self.gcode_li_max():
            self.layerUp( True )

        self.updatePlayState( self.play_timer_id is None )

    def layerUp( self, head ):
        self.scale_v_value.set( min( self.scale_v_value.get() + 1, self.gcode_ln_max() ) )
        self.scale_h.configure( from_ = 0, to = self.gcode_li_max() )

        if head:
            self.scale_h_value.set( 0 )
        else:
            self.scale_h_value.set( self.gcode_li_max() )

    def layerDown( self, head ):
        self.scale_v_value.set( max( self.scale_v_value.get() - 1, self.gcode_ln_min() ) )
        self.scale_h.configure( from_ = 0, to = self.gcode_li_max() )

        if head:
            self.scale_h_value.set( 0 )
        else:
            self.scale_h_value.set( self.gcode_li_max() )

    def onButton_btn_u( self, event = None ):
        self.layerUp( False )
        self.updateImage()

    def onButton_btn_d( self, event = None ):
        self.layerDown( False )
        self.updateImage()

    def onButton_btn_pp( self, event = None ):
        if self.gcode_li() == 0:
            self.layerDown( False )
        else:
            self.scale_h_value.set( 0 )

        self.updateImage()

    def onButton_btn_p( self, event = None ):
        if self.gcode_li() == 0:
            self.layerDown( False )
        else:
            self.scale_h_value.set( max( self.scale_h_value.get() - 1, 0 ) )

        self.updateImage()

    def onButton_btn_n( self, event = None ):
        if self.gcode_li() == self.gcode_li_max():
            self.layerUp( True )
        else:
            self.scale_h_value.set( min( self.scale_h_value.get() + 1, self.gcode_li_max() ) )
        self.updateImage()

    def onButton_btn_nn( self, event = None ):
        if self.gcode_li() == self.gcode_li_max():
            self.layerUp( True )
        else:
            self.scale_h_value.set( self.gcode_li_max() )

        self.updateImage()

    def openFile( self, filename ):
        self.updatePlayState( False )

        filenames = self.root.tk.splitlist( filename )

        if filenames is not None and len( filenames ) > 0:
            filename = filenames[ 0 ]

            self.updatePlayState( False )

            self.root.config( cursor="wait" )

            if False:
                # blocking

                try:
                    gl = GcodeLoader()
                    gl.load( filename )
                    self.setupGcode( gl, filename )
                    self.updateImage()

                except Exception as err:
                    self.loadError( err, filename )

                self.root.config( cursor="" )

            else:
                # threading

                self.loadProgressReposition( filename )

                self.thread_gl_filename = filename
                self.thread_gl = GcodeLoader()
                self.thread_gl_thread = threading.Thread( group=None, target = lambda x : x.load( filename ), args=( self.thread_gl, ) )
                self.thread_gl_thread.start()
                self.loadprog_th.delete( 'all' )
                self.loadprog_th.configure( width = 0, height = 0 )
                self.thread_gl_th_image = None
                self.root.after( self.thread_gl_ptm, self.loadProgress )

    def loadError( self, err, filename = "" ):
        traceback.print_exception( err, file=sys.stderr )
        msg = "File open error.\n[%s]\n%s" % ( filename, err )
        print( msg, file=sys.stderr )
        tkmb.showerror( "File open error", msg )

    def loadProgress( self ):
        if self.thread_gl_thread.is_alive():

            self.loadprog_loading_value.set( "Now Loading ...[%s]" % ( os.path.basename( self.thread_gl_filename ), ) )

            proc = self.thread_gl.getProc()

            if proc[0] != 0 and proc[1] != 0:

                if self.loadprog_progress.cget( 'mode' ) != 'determinate':
                    self.loadprog_progress.configure( mode = 'determinate' )

                per = proc[0] / proc[1]

                self.loadprog_progress_value.set( int( per * 100 ) )

                self.loadprog_size_value.set(
                    "%s / %s | %s / %s L %s [%d%%] " % (
                        format_size( proc[0] )
                    ,   format_size( proc[1] )
                    ,   format_time_minsec( proc[2] )
                    ,   format_time_minsec( proc[2] / per )
                    ,   format_time_minsec( proc[2] / per - proc[2] )
                    ,   int( per * 100 )
                    )
                )

            elif proc[0] != 0:

                if self.loadprog_progress.cget( 'mode' ) != 'indeterminate':
                    self.loadprog_progress.configure( mode = 'indeterminate' )
                    self.loadprog_progress.start()

                self.loadprog_size_value.set(
                    "%s | %s" % ( format_size( proc[0] ), format_time_minsec( proc[2] ) )
                )

            if self.thread_gl_th_image is None:

                thumbnail_bytes = self.thread_gl.getThumbnailImage()

                if thumbnail_bytes is not None:
                    self.thread_gl_th_image = ImageTk.PhotoImage( Image.open( io.BytesIO( thumbnail_bytes ) ) )

                    w = self.thread_gl_th_image.width()
                    h = self.thread_gl_th_image.height()

                    self.loadprog_th.configure( width = w, height = h )
                    self.loadprog_th.create_image( w / 2, h / 2, image = self.thread_gl_th_image, anchor=tk.CENTER, tag='all' )

            self.root.after( self.thread_gl_ptm, self.loadProgress )

        else:
            self.thread_gl_thread.join()

            self.root.config( cursor="" )

            self.hideLoadProgress()

            if self.thread_gl.err:
                self.loadError( self.thread_gl.err, self.thread_gl_filename )
            else:
                self.setupGcode( self.thread_gl, self.thread_gl_filename )
                self.updateImage()

            self.thread_gl          = None
            self.thread_gl_filename = None
            self.thread_gl_thread   = None
            self.loadprog_th.delete( 'all' )
            self.loadprog_th.configure( width = 0, height = 0 )
            self.thread_gl_th_image = None

    def onButton_btn_open( self, event = None ):
        self.openFile( tkfd.askopenfilename( filetypes = FILETYPES ) )

    def onDropFile( self, event ):
        self.openFile( event.data )

    def onButton_btn_test( self, event = None ):
        pass

    def run( self ):
        rt = self.root = tkdnd.Tk()

        self.setupIcons()
        self.setupWindow()
        self.setupGcode( GcodeLoader() )

        rt.wait_visibility()

        self.updateImage()

        rt.mainloop()

if __name__ == "__main__":
    viewer = Viewer()
    viewer.run()

# EOF
